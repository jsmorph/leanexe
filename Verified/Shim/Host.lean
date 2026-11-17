import LeanExe.Linux.Replies
import LeanExe.Wasi.CallTable
import Verified.Shim.Replies

/-!
The WASI host that the shim implements with the Linux call layer, for the stream functions
`fd_read` (descriptor 0), `fd_write` (descriptors 1 and 2), and `proc_exit`, and the flat calls of
`shimCalls`.

`Image F L I events e l` states which layer events `l` the shim makes for the WASI event `e` after
the layer events `events`, with the open flags `F`, the layout `L`, and the launch `I`: one `read`
of descriptor 0 with the request's
count and no input for an `fd_read`, one `write` of the stream's descriptor with the offered
bytes, fewer than `2^32`, and no prior output for an `fd_write`, none for an exit, and for a flat
call whose arguments its description accepts, the events of `SysImage`, one image for each call
of `shimCalls`.  A file function refuses a descriptor number outside `openNumbers I events`
with errno 8 (`badf`) and no call, and the prestat functions answer for descriptor 3 while
`preopened I events` holds.  The WASI reply follows from the events' results: a result in the
range that Linux gives for the request gives its count, descriptor, or time, a negated error
number gives `errnoOf` of the number, and any other result gives a trap of the shim.  An address
in linear memory and the bytes of an output region before a call depend on the store, which the
WASI event does not carry, so `Image` leaves them free.  `Images events es ls` states that `ls`
concatenates an image of each event of `es` in order, each after `events` and the images before
it, and `WritesWithin L size e` that each output region of `e` lies in the `size` bytes from the
guest's byte 0 or is the scratch's timespec.

`linuxHost F L I replies` relates a world and a WASI request to a reply and a world exactly when
the layer events that it appends are an image of the WASI event after the world's events, each
holds its reply of `replies`, counted from the number of events so far, and each writes within
the `2^32` bytes from the guest's byte 0, the guest's address space, or into the timespec.  The
host accepts an exit status below 126, which sets the exit marker, and rejects a status of 126 or
more, as the repository's Wasmtime host does.  The sizes of the regions of `args_get` and
`environ_get` come from `I`.  The world records the outputs of every successful flat call by its
name, from which a call that names another reporter takes its sizes, as `Host.sys_reports`
requires of every call.
-/

namespace Verified.Shim

open LeanExe LeanExe.Wasi Verified.Wasi

/-- `clock_time_get` of clock 0 or 1 makes one `clock_gettime` of the clock into the timespec,
which the stub clears before the call, and its reply is `clockReply` of the result; clocks 2 and 3,
the CPU-time clocks, give errno 8 (`badf`) without a call, as Wasmtime 44 answers. -/
def ClockImage (L : ShimLayout) (args : List Arg) (reply : Transfer (List Bytes))
    (l : List Linux.Event) : Prop :=
  match args with
  | [.word id, .word _] =>
    if id.toNat < 2 then ∃ ret output,
      l = [⟨Linux.clockGettimeCall, [id, L.timespec], [], List.replicate 16 0, ret, output⟩] ∧
        reply = clockReply ret output
    else l = [] ∧ reply = .returned 8 [zeros 8]
  | _ => False

/-- The `getrandom` events of `random_get`'s loop, which fills `length` bytes at `a` and has
filled the `done` bytes `filled`, and the reply that they give.  Each call asks for the bytes that
remain; a count between 1 and the remaining bytes, exclusive, adds the first bytes of its output,
as many as the count, and the loop goes on; any other result ends it with `randomLast`.  The loop
makes no call when no byte remains. -/
def RandomCalls (a : UInt64) (length : Nat) :
    Nat → List UInt8 → List Linux.Event → Transfer (List Bytes) → Prop
  | done, filled, [], reply => done = length ∧ reply = .returned 0 [bytesOfList filled]
  | done, filled, e :: l, reply => done < length ∧ ∃ prior ret output,
      e = ⟨Linux.getrandomCall, [a + UInt64.ofNat done, UInt64.ofNat (length - done), 0], [],
        prior, ret, output⟩ ∧
      if 0 < ret.toNat ∧ ret.toNat < length - done then
        RandomCalls a length (done + ret.toNat) (filled ++ output.take ret.toNat) l reply
      else l = [] ∧ reply = randomLast length (length - done) filled ret output

/-- `random_get` of `length` bytes makes the `getrandom` events of its loop into a buffer whose
address the image leaves free. -/
def RandomImage (args : List Arg) (reply : Transfer (List Bytes)) (l : List Linux.Event) : Prop :=
  match args with
  | [.space length] => ∃ a, RandomCalls a length.toNat 0 [] l reply
  | _ => False

/-- `args_sizes_get` and `environ_sizes_get` make no call and reply with the count and the size of
`strings`. -/
def SizesImage (strings : List (List UInt8)) (args : List Arg) (reply : Transfer (List Bytes))
    (l : List Linux.Event) : Prop :=
  args = [] ∧ l = [] ∧ reply = sizesReply strings

/-- `args_get` and `environ_get` make no call and reply with `strings`. -/
def StringsImage (strings : List (List UInt8)) (args : List Arg) (reply : Transfer (List Bytes))
    (l : List Linux.Event) : Prop :=
  args = [] ∧ l = [] ∧ reply = stringsReply strings

/-- The `openat2` events of `path_open` under `dir` with the path `path` and the record `how`, from
its call `calls`, and the reply that they give: a call that fails with `EAGAIN` (11) is made again
while fewer than four calls were made, as cap-std 3.4.5 does, and any other result ends the calls
with `openReply`. -/
def OpenCalls (L : ShimLayout) (dir : UInt64) (path how : List UInt8) :
    Nat → List Linux.Event → Transfer (List Bytes) → Prop
  | _, [], _ => False
  | calls, e :: l, reply => ∃ ret,
      e = ⟨Linux.openat2Call, [dir, L.path, L.openHow, 24], [path ++ [0], how], [], ret, []⟩ ∧
      if ret = 0 - 11 ∧ calls < 3 then OpenCalls L dir path how (calls + 1) l reply
      else l = [] ∧ reply = openReply ret

/-- `path_open` makes no call when `openCheck` gives an errno for the open numbers `opened`, and
otherwise the `openat2` events of `OpenCalls` with the path and the `open_how` record of the
request. -/
def OpenImage (F : OpenFlags) (L : ShimLayout) (opened : List UInt64) (args : List Arg)
    (reply : Transfer (List Bytes)) (l : List Linux.Event) : Prop :=
  match args with
  | [.word dir, .word dirflags, .bytes path, .word oflags, .word rights, .word _, .word fdflags] =>
    if openCheck opened dir oflags path fdflags = 0 then
      OpenCalls L dir path.data.data.toList (openHowBytes F dirflags oflags rights fdflags) 0 l reply
    else l = [] ∧ reply = .returned (openCheck opened dir oflags path fdflags) [zeros 4]
  | _ => False

/-- `fd_close` makes one `close` of its descriptor when `opened` holds it, and refuses it with
errno 8 (`badf`) otherwise. -/
def CloseImage (opened : List UInt64) (args : List Arg) (reply : Transfer (List Bytes))
    (l : List Linux.Event) : Prop :=
  match args with
  | [.word fd] =>
    if fd ∈ opened then
      ∃ ret, l = [⟨Linux.closeCall, [fd], [], [], ret, []⟩] ∧ reply = closeReply ret
    else l = [] ∧ reply = .returned 8 []
  | _ => False

/-- `fd_read` on a handle makes one `read` of its descriptor into a buffer of its capacity whose
address the image leaves free when `opened` holds the descriptor, and refuses it with errno 8
(`badf`) otherwise. -/
def HandleReadImage (opened : List UInt64) (args : List Arg) (reply : Transfer (List Bytes))
    (l : List Linux.Event) : Prop :=
  match args with
  | [.word fd, .space capacity] =>
    if fd ∈ opened then ∃ a prior ret output,
      l = [⟨Linux.readCall, [fd, a, capacity], [], prior, ret, output⟩] ∧
        reply = handleReadReply capacity ret output
    else l = [] ∧ reply = .returned 8 [zeros capacity.toNat, zeros 4]
  | _ => False

/-- `fd_write` on a handle makes one `write` of its descriptor with the offered bytes from an
address that the image leaves free when `opened` holds the descriptor, and refuses it with errno
8 (`badf`) otherwise. -/
def HandleWriteImage (opened : List UInt64) (args : List Arg) (reply : Transfer (List Bytes))
    (l : List Linux.Event) : Prop :=
  match args with
  | [.word fd, .bytes data] =>
    if fd ∈ opened then ∃ a ret,
      l = [⟨Linux.writeCall, [fd, a, UInt64.ofNat data.data.size], [data.data.data.toList], [],
        ret, []⟩] ∧ reply = handleWriteReply (UInt64.ofNat data.data.size) ret
    else l = [] ∧ reply = .returned 8 [zeros 4]
  | _ => False

/-- `fd_prestat_get` makes no call. -/
def PrestatImage (preopened : Bool) (args : List Arg) (reply : Transfer (List Bytes))
    (l : List Linux.Event) : Prop :=
  match args with
  | [.word fd] => l = [] ∧ reply = prestatReply preopened fd
  | _ => False

/-- `fd_prestat_dir_name` makes no call. -/
def DirNameImage (preopened : Bool) (opened : List UInt64) (args : List Arg)
    (reply : Transfer (List Bytes)) (l : List Linux.Event) : Prop :=
  match args with
  | [.word fd, .space capacity] => l = [] ∧ DirNameReply preopened opened fd capacity reply
  | _ => False

/-- The layer events `l` that the shim makes for the flat call `call` with the arguments `args`
and the reply `reply` after the layer events `events`: the image of the call among `shimCalls`,
and none for any other call. -/
def SysImage (F : OpenFlags) (L : ShimLayout) (I : Launch) (events : List Linux.Event) (call : Call)
    (args : List Arg) (reply : Transfer (List Bytes)) (l : List Linux.Event) : Prop :=
  if call = Call.clockTimeGet then ClockImage L args reply l
  else if call = Call.randomGet then RandomImage args reply l
  else if call = Call.argsSizesGet then SizesImage I.args args reply l
  else if call = Call.argsGet then StringsImage I.args args reply l
  else if call = Call.environSizesGet then SizesImage I.environ args reply l
  else if call = Call.environGet then StringsImage I.environ args reply l
  else if call = Call.pathOpen then OpenImage F L (openNumbers I events) args reply l
  else if call = Call.fdClose then CloseImage (openNumbers I events) args reply l
  else if call = Call.fdRead then HandleReadImage (openNumbers I events) args reply l
  else if call = Call.fdWrite then HandleWriteImage (openNumbers I events) args reply l
  else if call = Call.fdPrestatGet then PrestatImage (preopened I events) args reply l
  else if call = Call.fdPrestatDirName then
    DirNameImage (preopened I events) (openNumbers I events) args reply l
  else False

/-- The flat calls that the shim implements. -/
def shimCalls : List Call :=
  [Call.clockTimeGet, Call.randomGet, Call.argsSizesGet, Call.argsGet, Call.environSizesGet,
    Call.environGet, Call.pathOpen, Call.fdClose, Call.fdRead, Call.fdWrite, Call.fdPrestatGet,
    Call.fdPrestatDirName]

/-- The layer events `l` that the shim makes for the WASI event `e` after the layer events
`events`, with the buffer's address `a` and a read's prior bytes free. -/
def Image (F : OpenFlags) (L : ShimLayout) (I : Launch) (events : List Linux.Event) :
    Wasi.Event → List Linux.Event → Prop
  | .read count reply, l => ∃ e a, l = [e] ∧ e.call = Linux.readCall ∧
      e.args = [0, a, count] ∧ e.inputs = [] ∧ reply = readReply count e.ret e.output
  | .write output bytes reply, l => ∃ e a, l = [e] ∧ e.call = Linux.writeCall ∧
      e.args = [output.fd, a, UInt64.ofNat bytes.data.size] ∧
      e.inputs = [bytes.data.data.toList] ∧ e.prior = [] ∧ bytes.data.size < 2 ^ 32 ∧
      reply = writeReply (UInt64.ofNat bytes.data.size) e.ret
  | .exit _, l | .exitTrap _ _, l => l = []
  | .sys call args reply, l => call.reject args = 0 ∧ SysImage F L I events call args reply l

/-- `ls` concatenates an image of each event of `es`, in order, each after `events` and the images
before it. -/
inductive Images (F : OpenFlags) (L : ShimLayout) (I : Launch) :
    List Linux.Event → List Wasi.Event → List Linux.Event → Prop
  | nil {events : List Linux.Event} : Images F L I events [] []
  | cons {events : List Linux.Event} {e : Wasi.Event} {l : List Linux.Event}
      {es : List Wasi.Event} {ls : List Linux.Event} :
      Image F L I events e l → Images F L I (events ++ l) es ls →
        Images F L I events (e :: es) (l ++ ls)

/-- Each output region of the event `e` lies in the `size` bytes from the guest's byte 0, counted
modulo `2^64`, or is the scratch's timespec. -/
def WritesWithin (L : ShimLayout) (size : Nat) (e : Linux.Event) : Prop :=
  ∀ g ∈ Linux.outputRegions e.args 0 e.call.params,
    L.offset g.1 + g.2 ≤ size ∨ g = (L.timespec, 16)

/-- The event `e` holds the reply `r`: its result, and the reply's bytes over its output region,
as `Linux.step` records them. -/
def Carries (r : Linux.Reply) (e : Linux.Event) : Prop :=
  e.ret = r.ret ∧ e.output = match Linux.outputRegions e.args 0 e.call.params with
    | [] => []
    | g :: _ => (List.range g.2).map r.bytes

/-- Each event of `l` holds its reply of `replies`, the first the reply to call `k`. -/
def Carried (replies : Linux.Replies) : Nat → List Linux.Event → Prop
  | _, [] => True
  | k, e :: l => Carries (replies k) e ∧ Carried replies (k + 1) l

/-- The state of the host: the layer events so far, the exit marker, and the outputs of the last
successful flat call of each name. -/
structure LinuxWorld where
  events : List Linux.Event
  exited : Option UInt64
  reports : String → List Bytes

/-- The outputs of each name after the WASI event `e`: those of a flat call that returned errno 0
under its name, and the others kept. -/
def recordReports (reports : String → List Bytes) : Wasi.Event → String → List Bytes
  | .sys call _ (.returned errno outputs) => fun name =>
    if errno = 0 ∧ name = call.name then outputs else reports name
  | _ => reports

/-- The world after the shim answered the WASI event `e` with the layer events `l`. -/
def LinuxWorld.answer (w : LinuxWorld) (l : List Linux.Event) (e : Wasi.Event) : LinuxWorld :=
  ⟨w.events ++ l, w.exited, recordReports w.reports e⟩

/-- The shim answers the WASI event `e` from the world `w` with the world `w'`: it appends an
image of `e` whose events hold the replies from call `w.events.length` on and write within the
guest's address space or into the timespec. -/
def ShimStep (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies)
    (w : LinuxWorld) (e : Wasi.Event) (w' : LinuxWorld) : Prop :=
  ∃ l, Image F L I w.events e l ∧ Carried replies w.events.length l ∧
    (∀ x ∈ l, WritesWithin L (2 ^ 32) x) ∧ w' = w.answer l e

/-- The outputs from which a call with the reporter `name` takes its sizes: those of `I` for
`args_sizes_get` and `environ_sizes_get`, and the recorded outputs of every other name. -/
def reporterOutputs (I : Launch) (reports : String → List Bytes) (name : String) : List Bytes :=
  if name = "args_sizes_get" then sizesOutputs I.args
  else if name = "environ_sizes_get" then sizesOutputs I.environ
  else reports name

/-- The sizes of `call`'s reported regions. -/
def shimReported (I : Launch) (reports : String → List Bytes) (call : Call) : List Nat :=
  match call.reporter with
  | some name => call.sizesOf (reporterOutputs I reports name)
  | none => []

/-! ## The images of the calls -/

section Calls

variable {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
  {args : List Arg} {reply : Transfer (List Bytes)} {l : List Linux.Event}

theorem sysImage_clock :
    SysImage F L I events Call.clockTimeGet args reply l = ClockImage L args reply l := by
  simp (config := { decide := true }) only [SysImage, ↓reduceIte]

theorem sysImage_random :
    SysImage F L I events Call.randomGet args reply l = RandomImage args reply l := by
  simp (config := { decide := true }) only [SysImage, ↓reduceIte]

theorem sysImage_argsSizes :
    SysImage F L I events Call.argsSizesGet args reply l = SizesImage I.args args reply l := by
  simp (config := { decide := true }) only [SysImage, ↓reduceIte]

theorem sysImage_args :
    SysImage F L I events Call.argsGet args reply l = StringsImage I.args args reply l := by
  simp (config := { decide := true }) only [SysImage, ↓reduceIte]

theorem sysImage_environSizes :
    SysImage F L I events Call.environSizesGet args reply l = SizesImage I.environ args reply l := by
  simp (config := { decide := true }) only [SysImage, ↓reduceIte]

theorem sysImage_environ :
    SysImage F L I events Call.environGet args reply l = StringsImage I.environ args reply l := by
  simp (config := { decide := true }) only [SysImage, ↓reduceIte]

theorem sysImage_open :
    SysImage F L I events Call.pathOpen args reply l =
      OpenImage F L (openNumbers I events) args reply l := by
  simp (config := { decide := true }) only [SysImage, ↓reduceIte]

theorem sysImage_close :
    SysImage F L I events Call.fdClose args reply l =
      CloseImage (openNumbers I events) args reply l := by
  simp (config := { decide := true }) only [SysImage, ↓reduceIte]

theorem sysImage_read :
    SysImage F L I events Call.fdRead args reply l =
      HandleReadImage (openNumbers I events) args reply l := by
  simp (config := { decide := true }) only [SysImage, ↓reduceIte]

theorem sysImage_write :
    SysImage F L I events Call.fdWrite args reply l =
      HandleWriteImage (openNumbers I events) args reply l := by
  simp (config := { decide := true }) only [SysImage, ↓reduceIte]

theorem sysImage_prestat :
    SysImage F L I events Call.fdPrestatGet args reply l =
      PrestatImage (preopened I events) args reply l := by
  simp (config := { decide := true }) only [SysImage, ↓reduceIte]

theorem sysImage_dirName :
    SysImage F L I events Call.fdPrestatDirName args reply l =
      DirNameImage (preopened I events) (openNumbers I events) args reply l := by
  simp (config := { decide := true }) only [SysImage, ↓reduceIte]

/-- Only the calls of `shimCalls` have images. -/
theorem sysImage_mem {call : Call} (h : SysImage F L I events call args reply l) :
    call ∈ shimCalls := by
  by_contra outside
  simp only [shimCalls, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := outside
  simp only [SysImage, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, ↓reduceIte] at h

end Calls

/-! ## The host's laws -/

@[simp] theorem errnoOf_le (x : UInt64) : (errnoOf x).toNat ≤ 76 := (errnoOf_valid x).1

theorem outputs_read (x0 x1 x2 : UInt64) :
    Linux.outputRegions [x0, x1, x2] 0 Linux.readCall.params = [(x1, x2.toNat)] := rfl

theorem outputs_getrandom (x0 x1 x2 : UInt64) :
    Linux.outputRegions [x0, x1, x2] 0 Linux.getrandomCall.params = [(x0, x1.toNat)] := rfl

theorem outputs_clock (x0 x1 : UInt64) :
    Linux.outputRegions [x0, x1] 0 Linux.clockGettimeCall.params = [(x1, 16)] := rfl

/-- The reply carries outputs of the sizes `sizes` and an errno of at most 76. -/
def ReplyShape (sizes : List Nat) (reply : Transfer (List Bytes)) : Prop :=
  reply.committed.map (·.data.size) = sizes ∧ reply.validErrno

theorem clockReply_shape (ret : UInt64) (output : List UInt8) :
    ReplyShape [8] (clockReply ret output) := by
  unfold ReplyShape
  simp only [clockReply]
  split_ifs <;> simp [Transfer.committed, Transfer.validErrno]

theorem randomCalls_shape {replies : Linux.Replies} {a : UInt64} {length : Nat}
    (small : length < 2 ^ 64) :
    ∀ {done : Nat} {filled : List UInt8} {l : List Linux.Event} {reply : Transfer (List Bytes)}
      {k : Nat}, RandomCalls a length done filled l reply → Carried replies k l →
        filled.length = done → ReplyShape [length] reply
  | _, _, [], _, _, ⟨finished, rfl⟩, _, sized => by
    simp [ReplyShape, Transfer.committed, Transfer.validErrno, sized, finished]
  | done, filled, _ :: l, reply, k, ⟨below, prior, ret, output, rfl, rest⟩, ⟨carries, carried⟩,
      sized => by
    have count : output.length = length - done := by
      have out := carries.2
      simp only [outputs_getrandom] at out
      have wide : (UInt64.ofNat (length - done)).toNat = length - done :=
        UInt64.toNat_ofNat_of_lt' (show length - done < 2 ^ 64 by omega)
      rw [out, List.length_map, List.length_range, wide]
    split at rest
    · rename_i inside
      exact randomCalls_shape small rest carried (by simp [sized, count]; omega)
    · obtain ⟨rfl, rfl⟩ := rest
      unfold randomLast ReplyShape
      split_ifs
      · simp [Transfer.committed, Transfer.validErrno, sized, count]
        omega
      all_goals simp [Transfer.committed, Transfer.validErrno]

theorem sizesReply_shape (strings : List (List UInt8)) : ReplyShape [4, 4] (sizesReply strings) := by
  unfold sizesReply ReplyShape
  split_ifs <;> simp [Transfer.committed, Transfer.validErrno, sizesOutputs]

theorem stringsBytes_length (strings : List (List UInt8)) :
    (stringsBytes strings).length = stringsSize strings := by
  induction strings with
  | nil => rfl
  | cons s strings ih =>
    simp only [stringsBytes, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, stringsSize, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

/-- The size of the shown region of a call with the parameters of `args_get` for the outputs of
`strings`' sizes. -/
theorem strings_reported {call : Call}
    (params : call.params = [.reported 4 4 false, .reported 1 1 true]) (strings : List (List UInt8)) :
    call.outputSizes (call.sizesOf (sizesOutputs strings)) [] =
      [(littleEndian (leBytes 4 (stringsSize strings))).toNat] := by
  simp [Call.outputSizes, Call.sizesOf, params, outputSizesOf, reportedSizesOf, sizesOutputs]

theorem shimReported_args (I : Launch) (reports : String → List Bytes) :
    shimReported I reports Call.argsGet = Call.argsGet.sizesOf (sizesOutputs I.args) := by
  simp (config := { decide := true }) [shimReported, reporterOutputs, Call.argsGet]

theorem shimReported_environ (I : Launch) (reports : String → List Bytes) :
    shimReported I reports Call.environGet = Call.environGet.sizesOf (sizesOutputs I.environ) := by
  simp (config := { decide := true }) [shimReported, reporterOutputs, Call.environGet]

theorem stringsReply_shape (strings : List (List UInt8)) :
    ReplyShape [(littleEndian (leBytes 4 (stringsSize strings))).toNat] (stringsReply strings) := by
  unfold stringsReply ReplyShape
  split_ifs with fits
  · simp only [stringsFit, decide_eq_true_eq] at fits
    have small : stringsSize strings < 2 ^ (8 * 4) := by omega
    simp [Transfer.committed, Transfer.validErrno, stringsBytes_length,
      littleEndian_leBytes (n := 4) (by omega) small,
      UInt64.toNat_ofNat_of_lt' (show stringsSize strings < 2 ^ 64 by omega)]
  · simp [Transfer.committed, Transfer.validErrno]

theorem openCheck_le (opened : List UInt64) (dir oflags : UInt64) (path : Bytes)
    (fdflags : UInt64) : (openCheck opened dir oflags path fdflags).toNat ≤ 76 := by
  unfold openCheck
  split_ifs <;> decide

theorem openReply_shape (ret : UInt64) : ReplyShape [4] (openReply ret) := by
  unfold openReply ReplyShape
  split_ifs <;> simp [Transfer.committed, Transfer.validErrno]

theorem openCalls_shape {L : ShimLayout} {dir : UInt64} {path how : List UInt8} :
    ∀ {calls : Nat} {l : List Linux.Event} {reply : Transfer (List Bytes)},
      OpenCalls L dir path how calls l reply → ReplyShape [4] reply
  | _, [], _, h => h.elim
  | _, _ :: _, _, ⟨ret, _, rest⟩ => by
    split at rest
    · exact openCalls_shape rest
    · obtain ⟨rfl, rfl⟩ := rest
      exact openReply_shape ret

theorem closeReply_shape (ret : UInt64) : ReplyShape [] (closeReply ret) := by
  unfold closeReply ReplyShape
  split_ifs <;> simp [Transfer.committed, Transfer.validErrno]

theorem handleReadReply_shape (capacity ret : UInt64) (output : List UInt8)
    (sized : output.length = capacity.toNat) :
    ReplyShape [capacity.toNat, 4] (handleReadReply capacity ret output) := by
  unfold handleReadReply ReplyShape
  split_ifs <;> simp [Transfer.committed, Transfer.validErrno, sized]

theorem handleWriteReply_shape (count ret : UInt64) :
    ReplyShape [4] (handleWriteReply count ret) := by
  unfold handleWriteReply ReplyShape
  split_ifs <;> simp [Transfer.committed, Transfer.validErrno]

theorem prestatReply_shape (preopened : Bool) (fd : UInt64) :
    ReplyShape [8] (prestatReply preopened fd) := by
  unfold prestatReply ReplyShape
  split_ifs <;> simp [Transfer.committed, Transfer.validErrno]

theorem dirNameReply_shape {preopened : Bool} {opened : List UInt64} {fd capacity : UInt64}
    {reply : Transfer (List Bytes)} (h : DirNameReply preopened opened fd capacity reply) :
    ReplyShape [capacity.toNat] reply := by
  unfold DirNameReply at h
  unfold ReplyShape
  split_ifs at h with h1 h2 h3
  · obtain ⟨rest, length, rfl⟩ := h
    simp [Transfer.committed, Transfer.validErrno, length]
    omega
  all_goals (subst h; simp [Transfer.committed, Transfer.validErrno])

/-- A flat call's reply in an image carries outputs of the sizes of the call's description, with
the sizes of the reported regions that `I` gives, and an errno of at most 76. -/
theorem sysImage_shape {F : OpenFlags} {L : ShimLayout} {I : Launch} {replies : Linux.Replies}
    {events : List Linux.Event} {call : Call} {args : List Arg} {reply : Transfer (List Bytes)}
    {l : List Linux.Event} {k : Nat}
    (image : SysImage F L I events call args reply l) (carried : Carried replies k l)
    (reports : String → List Bytes) :
    ReplyShape (call.outputSizes (shimReported I reports call) args) reply := by
  have member := sysImage_mem image
  simp only [shimCalls, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [sysImage_clock] at image
    unfold ClockImage at image
    split at image
    · change ReplyShape [8] reply
      split at image
      · obtain ⟨ret, output, rfl, rfl⟩ := image
        exact clockReply_shape ret output
      · obtain ⟨rfl, rfl⟩ := image
        simp [ReplyShape, Transfer.committed, Transfer.validErrno]
    · exact image.elim
  · rw [sysImage_random] at image
    unfold RandomImage at image
    split at image
    · rename_i length
      obtain ⟨a, image⟩ := image
      exact randomCalls_shape length.toNat_lt image carried rfl
    · exact image.elim
  · rw [sysImage_argsSizes] at image
    obtain ⟨rfl, rfl, rfl⟩ := image
    exact sizesReply_shape _
  · rw [sysImage_args] at image
    obtain ⟨rfl, rfl, rfl⟩ := image
    rw [shimReported_args, strings_reported rfl]
    exact stringsReply_shape _
  · rw [sysImage_environSizes] at image
    obtain ⟨rfl, rfl, rfl⟩ := image
    exact sizesReply_shape _
  · rw [sysImage_environ] at image
    obtain ⟨rfl, rfl, rfl⟩ := image
    rw [shimReported_environ, strings_reported rfl]
    exact stringsReply_shape _
  · rw [sysImage_open] at image
    unfold OpenImage at image
    split at image
    · change ReplyShape [4] reply
      split at image
      · exact openCalls_shape image
      · obtain ⟨rfl, rfl⟩ := image
        simp [ReplyShape, Transfer.committed, Transfer.validErrno, openCheck_le]
    · exact image.elim
  · rw [sysImage_close] at image
    unfold CloseImage at image
    split at image
    · change ReplyShape [] reply
      split at image
      · obtain ⟨ret, rfl, rfl⟩ := image
        exact closeReply_shape ret
      · obtain ⟨rfl, rfl⟩ := image
        simp [ReplyShape, Transfer.committed, Transfer.validErrno]
    · exact image.elim
  · rw [sysImage_read] at image
    unfold HandleReadImage at image
    split at image
    · rename_i fd capacity
      change ReplyShape [capacity.toNat, 4] reply
      split at image
      · obtain ⟨a, prior, ret, output, rfl, rfl⟩ := image
        have out := carried.1.2
        simp only [outputs_read] at out
        exact handleReadReply_shape capacity ret output (by simp [out])
      · obtain ⟨rfl, rfl⟩ := image
        simp [ReplyShape, Transfer.committed, Transfer.validErrno]
    · exact image.elim
  · rw [sysImage_write] at image
    unfold HandleWriteImage at image
    split at image
    · change ReplyShape [4] reply
      split at image
      · obtain ⟨a, ret, rfl, rfl⟩ := image
        exact handleWriteReply_shape _ ret
      · obtain ⟨rfl, rfl⟩ := image
        simp [ReplyShape, Transfer.committed, Transfer.validErrno]
    · exact image.elim
  · rw [sysImage_prestat] at image
    unfold PrestatImage at image
    split at image
    · obtain ⟨rfl, rfl⟩ := image
      exact prestatReply_shape _ _
    · exact image.elim
  · rw [sysImage_dirName] at image
    unfold DirNameImage at image
    split at image
    · obtain ⟨rfl, image⟩ := image
      exact dirNameReply_shape image
    · exact image.elim

/-- The outputs of a successful `args_sizes_get` or `environ_sizes_get` in an image are those of
`I`. -/
theorem sysImage_reporter {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {events : List Linux.Event} {call : Call} {args : List Arg} {outputs : List Bytes}
    {l : List Linux.Event} (image : SysImage F L I events call args (.returned 0 outputs) l) :
    (call.name = "args_sizes_get" → outputs = sizesOutputs I.args) ∧
      (call.name = "environ_sizes_get" → outputs = sizesOutputs I.environ) := by
  have member := sysImage_mem image
  simp only [shimCalls, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact ⟨fun named => absurd named (by decide), fun named => absurd named (by decide)⟩
    | skip
  · rw [sysImage_argsSizes] at image
    obtain ⟨_, _, same⟩ := image
    refine ⟨fun _ => ?_, fun named => absurd named (by decide)⟩
    unfold sizesReply at same
    split_ifs at same
    · exact (Transfer.returned.inj same).2
    · exact absurd (Transfer.returned.inj same).1 (by decide)
  · rw [sysImage_environSizes] at image
    obtain ⟨_, _, same⟩ := image
    refine ⟨fun named => absurd named (by decide), fun _ => ?_⟩
    unfold sizesReply at same
    split_ifs at same
    · exact (Transfer.returned.inj same).2
    · exact absurd (Transfer.returned.inj same).1 (by decide)

/-- The WASI host of the shim: the stream functions and the flat calls answered by `ShimStep`, an
exit status below 126 accepted, and a status of 126 or more rejected. -/
def linuxHost (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies) :
    Host LinuxWorld where
  exited w := w.exited
  read w count reply w' := ShimStep F L I replies w (.read count reply) w'
  write w output bytes reply w' := ShimStep F L I replies w (.write output bytes reply) w'
  exit w code w' := code.toNat < 126 ∧ w' = { w with exited := some code }
  exitTrap w code message w' := 126 ≤ code.toNat ∧ message = exitRejected ∧ w' = w
  read_bound h := by
    obtain ⟨_, ⟨e, a, rfl, _, _, _, rfl⟩, _⟩ := h
    exact readReply_valid _ _ _
  write_bound h := by
    obtain ⟨_, ⟨e, a, rfl, _, _, _, _, _, rfl⟩, _⟩ := h
    exact writeReply_valid _ _
  read_exited h := by
    obtain ⟨_, _, _, _, rfl⟩ := h
    rfl
  write_exited h := by
    obtain ⟨_, _, _, _, rfl⟩ := h
    rfl
  exit_recorded h := by
    obtain ⟨_, rfl⟩ := h
    rfl
  exitTrap_exited h := by
    obtain ⟨_, _, rfl⟩ := h
    rfl
  sys w call args reply w' := ShimStep F L I replies w (.sys call args reply) w'
  reported w call := shimReported I w.reports call
  sys_bound h := by
    obtain ⟨_, ⟨_, image⟩, carried, _, _⟩ := h
    exact sysImage_shape image carried _
  sys_exited h := by
    obtain ⟨_, _, _, _, rfl⟩ := h
    rfl
  sys_reports h named := by
    obtain ⟨_, ⟨_, image⟩, _, _, rfl⟩ := h
    have outputs := sysImage_reporter image
    simp only [shimReported, named, LinuxWorld.answer, recordReports, reporterOutputs, and_self,
      ↓reduceIte]
    split_ifs with first second
    · rw [outputs.1 first]
    · rw [outputs.2 second]
    · rfl

end Verified.Shim
