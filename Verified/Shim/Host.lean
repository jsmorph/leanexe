import LeanExe.Linux.Replies
import Verified.Shim.Memory

/-!
The WASI host that the shim implements with the Linux call layer, for the stream functions
`fd_read` (descriptor 0), `fd_write` (descriptors 1 and 2), and `proc_exit`.

`Image e l` states which layer events `l` the shim makes for the WASI event `e`: one `read` of
descriptor 0 with the request's count and no input for an `fd_read`, one `write` of the stream's
descriptor with the offered bytes, fewer than `2^32`, and no prior output for an `fd_write`, and
none for an exit.  The WASI reply follows from the event's result.  A result at most the request's
count is a count of bytes, a negated error number gives `errnoOf` of the number, and any other
result, which Linux never gives for the request, gives a trap of the shim.  The address of the
buffer and a read's prior bytes depend on the store, which the WASI event does not carry, so
`Image` leaves them free.  `Images es ls` states that `ls` concatenates an image of each event of
`es` in order, and `WritesWithin L size e` that the output region of `e` lies in the `size` bytes
from the guest's byte 0.

`linuxHost L replies` relates a world and a WASI request to a reply and a world exactly when the
layer events that it appends are an image of the WASI event, each holds its reply of `replies`,
counted from the number of events so far, and each writes within the `2^32` bytes from the
guest's byte 0, the guest's address space.  The host accepts an exit status below 126, which sets
the exit marker, and rejects a status of 126 or more, as the repository's Wasmtime host does.
-/

namespace Verified.Shim

open LeanExe LeanExe.Wasi Verified.Wasi

/-- The WASI errno of the Linux error number `x`, by Wasmtime 44's table, with `EXDEV` as `perm`,
the errno that cap-std gives an escape, and `io` for every other number.  Wasmtime converts a
stream's error with `from_raw_os_error` of `crates/wasi/src/p2/host/filesystem.rs` and the
conversion of its codes in `crates/wasi/src/p1.rs`, and a descriptor's error with the table of
the same arms in `crates/wasi/src/filesystem.rs`; a number outside the arms falls back to the
error's kind, which gives a code other than `io` only for numbers that the arms name. -/
def errnoOf (x : UInt64) : UInt64 :=
  match x.toNat with
  | 1 => 63 -- EPERM: perm
  | 2 => 44 -- ENOENT: noent
  | 4 => 27 -- EINTR: intr
  | 5 => 29 -- EIO: io
  | 9 => 8 -- EBADF: badf
  | 12 => 48 -- ENOMEM: nomem
  | 13 => 2 -- EACCES: acces
  | 16 => 10 -- EBUSY: busy
  | 17 => 20 -- EEXIST: exist
  | 18 => 63 -- EXDEV: perm
  | 20 => 54 -- ENOTDIR: notdir
  | 21 => 31 -- EISDIR: isdir
  | 22 => 28 -- EINVAL: inval
  | 27 => 22 -- EFBIG: fbig
  | 28 => 51 -- ENOSPC: nospc
  | 29 => 70 -- ESPIPE: spipe
  | 31 => 34 -- EMLINK: mlink
  | 32 => 64 -- EPIPE: pipe
  | 36 => 37 -- ENAMETOOLONG: nametoolong
  | 39 => 55 -- ENOTEMPTY: notempty
  | 40 => 32 -- ELOOP: loop
  | 75 => 61 -- EOVERFLOW: overflow
  | 84 => 25 -- EILSEQ: ilseq
  | 95 => 58 -- EOPNOTSUPP: notsup
  | 114 => 7 -- EALREADY: already
  | 115 => 26 -- EINPROGRESS: inprogress
  | _ => 29

theorem errnoOf_valid (x : UInt64) : (errnoOf x).toNat ≤ 76 ∧ errnoOf x ≠ 0 := by
  unfold errnoOf
  split <;> decide

/-- The message of a trap of the shim: a request that no contract admits, or a Linux result that
Linux never gives for the request. -/
def shimTrap : String := "linux shim"

/-- The message of an exit status of 126 or more, which the shim rejects. -/
def exitRejected : String := "linux shim: exit status 126 or more"

/-- The reply to an `fd_read` of `count` bytes whose `read` returned `ret` with the bytes `output`
in its buffer: the first `ret` bytes when `ret` is at most `count`, the errno of a negated error
number, and a trap of the shim for any other result. -/
def readReply (count ret : UInt64) (output : List UInt8) : Transfer Bytes :=
  if ret.toNat ≤ count.toNat then .returned 0 (bytesOfList (output.take ret.toNat))
  else if Linux.isError ret then .returned (errnoOf (0 - ret)) Bytes.empty
  else .trapped shimTrap Bytes.empty

/-- The reply to an `fd_write` of `count` bytes whose `write` returned `ret`: the count `ret` when
it is at most `count`, the errno of a negated error number, and a trap of the shim for any other
result. -/
def writeReply (count ret : UInt64) : Transfer UInt64 :=
  if ret.toNat ≤ count.toNat then .returned 0 ret
  else if Linux.isError ret then .returned (errnoOf (0 - ret)) 0
  else .trapped shimTrap 0

/-- The layer events `l` that the shim makes for the WASI event `e`, with the buffer's address `a`
and a read's prior bytes free. -/
def Image : Wasi.Event → List Linux.Event → Prop
  | .read count reply, l => ∃ e a, l = [e] ∧ e.call = Linux.readCall ∧
      e.args = [0, a, count] ∧ e.inputs = [] ∧ reply = readReply count e.ret e.output
  | .write output bytes reply, l => ∃ e a, l = [e] ∧ e.call = Linux.writeCall ∧
      e.args = [output.fd, a, UInt64.ofNat bytes.data.size] ∧
      e.inputs = [bytes.data.data.toList] ∧ e.prior = [] ∧ bytes.data.size < 2 ^ 32 ∧
      reply = writeReply (UInt64.ofNat bytes.data.size) e.ret
  | .exit _, l | .exitTrap _ _, l => l = []
  | .sys .., _ => False

/-- `ls` concatenates an image of each event of `es`, in order. -/
inductive Images : List Wasi.Event → List Linux.Event → Prop
  | nil : Images [] []
  | cons {e : Wasi.Event} {l : List Linux.Event} {es : List Wasi.Event} {ls : List Linux.Event} :
      Image e l → Images es ls → Images (e :: es) (l ++ ls)

/-- The output region of the event `e` lies in the `size` bytes from the guest's byte 0, counted
modulo `2^64`. -/
def WritesWithin (L : ShimLayout) (size : Nat) (e : Linux.Event) : Prop :=
  ∀ g ∈ Linux.outputRegions e.args 0 e.call.params, L.offset g.1 + g.2 ≤ size

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

/-- The state of the host: the layer events so far and the exit marker. -/
structure LinuxWorld where
  events : List Linux.Event
  exited : Option UInt64

/-- The shim answers the WASI event `e` from the world `w` with the world `w'`: it appends an
image of `e` whose events hold the replies from call `w.events.length` on and write within the
guest's address space. -/
def ShimStep (L : ShimLayout) (replies : Linux.Replies) (w : LinuxWorld) (e : Wasi.Event)
    (w' : LinuxWorld) : Prop :=
  ∃ l, Image e l ∧ Carried replies w.events.length l ∧
    (∀ x ∈ l, WritesWithin L (2 ^ 32) x) ∧
    w' = ⟨w.events ++ l, w.exited⟩

theorem readReply_valid (count ret : UInt64) (output : List UInt8) :
    (readReply count ret output).committed.data.size ≤ count.toNat ∧
      (readReply count ret output).validErrno := by
  unfold readReply
  split
  · refine ⟨?_, by simp [Transfer.validErrno]⟩
    simp only [Transfer.committed, bytesOfList_size, List.length_take]
    omega
  · split
    · exact ⟨Nat.zero_le _, (errnoOf_valid _).1⟩
    · exact ⟨Nat.zero_le _, trivial⟩

theorem writeReply_valid (size : Nat) (ret : UInt64) :
    (writeReply (UInt64.ofNat size) ret).committed.toNat ≤ size ∧
      (writeReply (UInt64.ofNat size) ret).validErrno := by
  unfold writeReply
  split
  · refine ⟨?_, by simp [Transfer.validErrno]⟩
    simp only [Transfer.committed, UInt64.toNat_ofNat'] at *
    have := Nat.mod_le size (2 ^ 64)
    omega
  · split
    · exact ⟨Nat.zero_le _, (errnoOf_valid _).1⟩
    · exact ⟨Nat.zero_le _, trivial⟩

/-- The WASI host of the shim: the stream functions answered by `ShimStep`, an exit status below
126 accepted, and a status of 126 or more rejected. -/
def linuxHost (L : ShimLayout) (replies : Linux.Replies) : Host LinuxWorld where
  exited w := w.exited
  read w count reply w' := ShimStep L replies w (.read count reply) w'
  write w output bytes reply w' := ShimStep L replies w (.write output bytes reply) w'
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

end Verified.Shim
