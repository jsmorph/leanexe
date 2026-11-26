module

public import Demos.ManifestCheck.Spec
public import Library.Hashing.Sha2.Equiv.SHA256.Main
public import LeanExe.Wasi.Bracket
public import LeanExe.Wasi.Semantics
public import LeanExe.Wasi.Sys
public import LeanExe.Wasi.WriteAll

@[expose] public section

/-! The specification of the runs of the manifest checker's WASI command, in terms of the events of
a run, `LeanExe.Wasi.Event`, which record each call with the reply that the host gave.

`Meets host world events code` states what the request asks of a run from `world` whose events
before its exit are `events` and whose status is `code`.  It holds three properties.

- `Run`, the verdicts and the status.  The run starts with the events of `args`.  An errno of
  `args` is the status, and an argument buffer without exactly one argument after the program name
  (`OneArgument`) gives status 1, each with no other event.  `ManifestRun` states the open of the
  manifest that the argument names, the call of `fd_filestat_get` on its descriptor, the reads of
  its bytes, and its close, and the status that they give: the errno of a call that fails, 61
  (`overflow`) for a reported size of `2^32` bytes or more, or 1 when the bytes number fewer or more
  than the size that `fd_filestat_get` reported.  A manifest
  without a line, or with a line outside `sha256sum`'s format, gives status 1.  Otherwise `Checks`
  states the check of each line in order: `FileCheck`, the open of its name, the reads of the file,
  its close, and its verdict, and then `LineWrites`, the writes of its output line.
- `Confined`: every `path_open` is relative to descriptor 3, with read-only rights, and names the
  argument or the name of a line of the manifest in `sha256sum`'s format.
- `Handled`: the run's events are calls of `args_sizes_get` and `args_get`, opens that fail,
  brackets of an open that returns errno 0, calls on its descriptor, and its close, and writes to
  standard output.

A line's verdict is OK exactly when the open of its name returned errno 0, a read returned no bytes
before any read returned an errno, the close returned errno 0, and the line's digits give the
digest of FIPS 180-4 of the bytes that the reads returned (`DigestOf`).  After a manifest that the
pure core accepts, the status is 0 exactly when every line's output line was written whole and
every verdict is OK, 1 when a verdict is FAILED and every output line was written whole, 77 after
writes of an output line, one more than its bytes, that each returned errno 0 and left bytes, and
the errno of a write that failed.

`SoFar host world events` states the three properties of the events of a run that stopped
without an accepted exit: at a trap of the host, at an exit that the host rejected, or at a trap of
the guest.  `ConfinedSoFar` states `Confined` of them for the buffer that `args` returned and the
bytes of a `ManifestRun` with status 0 that follows the events of `args` and whose manifest the
pure core accepts, or for no bytes.  `HandledSoFar` states that they are those of `Handled`
followed by those of `Unfinished`: none, an open that returned errno 0 with calls on its descriptor
and no close, an open that trapped, or an exit that the host rejected.  `VerdictsSoFar` states
that no event writes to standard output, or that the events are those of `args`, of a
`ManifestRun` with status 0 of a manifest that the pure core accepts, and of `ChecksSoFar` for its
lines, followed by events that write nothing to standard output.  `ChecksSoFar` states the checks
of the first lines as `Checks` states them, each with its verdict and the writes of its whole
output line, followed by none or by the `FileCheck` of the next line and writes that offer the
bytes of its output line, with that line's verdict, after those that the writes before them
took. -/

namespace Demos.ManifestCheck

open LeanExe LeanExe.Wasi SHS.Equiv.SHA256.Digest SHS.Equiv.SHA256.Padding.ByteDecoding
  SHS.Equiv.SHA256.Pipeline

/-- The bytes `bs` as a byte string. -/
def bytesOf (bs : List UInt8) : Bytes := ⟨⟨bs.toArray⟩⟩

/-- The argument buffer `buffer` holds a program name and exactly one argument, `name`, each
followed by a zero byte. -/
def OneArgument (buffer name : List UInt8) : Prop :=
  ∃ program, buffer = program ++ 0 :: (name ++ [0]) ∧ (0 : UInt8) ∉ program ∧ (0 : UInt8) ∉ name

/-- The rights of the manifest's open: `fd_read` (2) and `fd_filestat_get` (`2^21`). -/
def manifestRights : UInt64 := 2097154

/-- The rights of the open of a checked file: `fd_read` (2). -/
def fileRights : UInt64 := 2

/-- The arguments of the open of `name` with the rights `rights`: the directory 3, the flag
`symlink_follow` (1), no open flags, no inherited rights, and no descriptor flags. -/
def openArgs (rights : UInt64) (name : List UInt8) : List Arg :=
  [.word 3, .word 1, .bytes (bytesOf name), .word 0, .word rights, .word 0, .word 0]

/-- The event of a read of descriptor `fd` into a window of `length` bytes that returned `errno` and
the outputs `outputs`. -/
def readEvent (fd length errno : UInt64) (outputs : List Bytes) : Event :=
  .sys .fdRead [.word fd, .space length] (.returned errno outputs)

/-- The bytes that a read into a window of `length` bytes returned with errno 0 and the outputs
`outputs`: the first bytes of the window, as many as the count that the host returned, and at most
`length`. -/
def returned (length : UInt64) (outputs : List Bytes) : List UInt8 :=
  ((⟨0, outputs⟩ : Reply).bytes 0).data.data.toList.take
    (Min.min ((⟨0, outputs⟩ : Reply).word 1) length).toNat

/-- The event of `fd_filestat_get` of descriptor `fd` that returned `errno` and `outputs`. -/
def statEvent (fd errno : UInt64) (outputs : List Bytes) : Event :=
  .sys .fdFilestatGet [.word fd] (.returned errno outputs)

/-- The size that a reply of `fd_filestat_get` with errno 0 and the outputs `outputs` reports: the
field `size` of the record `filestat`, its eight bytes from byte 32. -/
def statSize (outputs : List Bytes) : UInt64 := (⟨0, outputs⟩ : Reply).field 0 32 8

/-- `ManifestReads fd size held events bytes status`: `events` are the reads of descriptor `fd`
into a buffer of `size` bytes after the bytes `held`, each into the window of the bytes that
follow those already read, and `bytes` are `held` followed by the bytes that they returned.  Each
read but the last returned errno 0 and at least one byte.  The reads end with status 0 when the
bytes fill the buffer, 1 when a read returned no bytes before the bytes filled the buffer, and the
errno of a read that failed. -/
inductive ManifestReads (fd : UInt64) (size : Nat) :
    List UInt8 → List Event → List UInt8 → UInt64 → Prop
  | full {held : List UInt8} (filled : held.length = size) :
      ManifestReads fd size held [] held 0
  | short {held : List UInt8} {outputs : List Bytes} (left : held.length < size)
      (empty : returned (UInt64.ofNat (size - held.length)) outputs = []) :
      ManifestReads fd size held [readEvent fd (UInt64.ofNat (size - held.length)) 0 outputs] held 1
  | failed {held : List UInt8} {errno : UInt64} {outputs : List Bytes} (left : held.length < size)
      (nonzero : errno ≠ 0) :
      ManifestReads fd size held
        [readEvent fd (UInt64.ofNat (size - held.length)) errno outputs] held errno
  | more {held : List UInt8} {outputs : List Bytes} {events : List Event} {bytes : List UInt8}
      {status : UInt64} (left : held.length < size)
      (nonempty : returned (UInt64.ofNat (size - held.length)) outputs ≠ [])
      (rest : ManifestReads fd size (held ++ returned (UInt64.ofNat (size - held.length)) outputs)
        events bytes status) :
      ManifestReads fd size held
        (readEvent fd (UInt64.ofNat (size - held.length)) 0 outputs :: events) bytes status

/-- `ManifestBody fd events status bytes`: `events` are those of the reading of the manifest open at
descriptor `fd`, `status` is its status, and, when the status is 0, `bytes` are the manifest's
bytes.  The call of `fd_filestat_get` comes first, and its errno ends the reading.  A reported size
of `2^32` bytes or more, more than the 32-bit length of a read allows, ends it with status 61
(`overflow`).  Otherwise the reads of `ManifestReads` follow for a buffer of the size that it
reported, and a status other than 0 ends the reading.  When the bytes fill the buffer, a last read
of 65,536 bytes follows, and the status is its errno when it is not 0, and otherwise 1 when it
returned bytes and 0 when it returned none. -/
inductive ManifestBody (fd : UInt64) : List Event → UInt64 → List UInt8 → Prop
  | statFailed {errno : UInt64} {outputs : List Bytes} (nonzero : errno ≠ 0) :
      ManifestBody fd [statEvent fd errno outputs] errno []
  | tooLarge {outputs : List Bytes} (large : 2 ^ 32 ≤ (statSize outputs).toNat) :
      ManifestBody fd [statEvent fd 0 outputs] 61 []
  | stopped {outputs : List Bytes} {events : List Event} {held : List UInt8} {status : UInt64}
      (small : (statSize outputs).toNat < 2 ^ 32)
      (reads : ManifestReads fd (statSize outputs).toNat [] events held status)
      (nonzero : status ≠ 0) :
      ManifestBody fd (statEvent fd 0 outputs :: events) status []
  | probed {outputs : List Bytes} {events : List Event} {bytes : List UInt8} {errno : UInt64}
      {last : List Bytes} (small : (statSize outputs).toNat < 2 ^ 32)
      (reads : ManifestReads fd (statSize outputs).toNat [] events bytes 0) :
      ManifestBody fd (statEvent fd 0 outputs :: events ++ [readEvent fd 65536 errno last])
        (if errno ≠ 0 then errno else if returned 65536 last ≠ [] then 1 else 0) bytes

/-- `ManifestRun name events status bytes`: `events` are those of the open of the manifest `name`,
its reading, and its close, `status` is their status, and, when the status is 0, `bytes` are the
manifest's bytes.  An open that returns an errno ends with that errno.  Otherwise the events of
`ManifestBody` follow on the opened descriptor, and its close, and the status is that of the body
when it is not 0, and else the errno of the close. -/
inductive ManifestRun (name : List UInt8) : List Event → UInt64 → List UInt8 → Prop
  | refused {errno : UInt64} {outputs : List Bytes} (nonzero : errno ≠ 0) :
      ManifestRun name [.sys .pathOpen (openArgs manifestRights name) (.returned errno outputs)]
        errno []
  | opened {outputs : List Bytes} {body : List Event} {status closeErrno : UInt64}
      {bytes : List UInt8} {committed : List Bytes}
      (reading : ManifestBody (openedDescriptor outputs) body status bytes) :
      ManifestRun name
        (.sys .pathOpen (openArgs manifestRights name) (.returned 0 outputs) :: body ++
          [.sys .fdClose [.word (openedDescriptor outputs)] (.returned closeErrno committed)])
        (if status ≠ 0 then status else closeErrno) bytes

/-- How the reads of a checked file ended: a read returned no bytes, a read returned an errno, or
the reads stopped before either. -/
inductive Ending where
  | eof
  | failed (errno : UInt64)
  | cut
  deriving DecidableEq

/-- The length of the window of a read of a checked file after the bytes `done`: the bytes of the
read buffer of 65,536 bytes after those that it holds, `done.length % 65536`. -/
def window (done : List UInt8) : UInt64 := UInt64.ofNat (65536 - done.length % 65536)

/-- `FileReads fd r done events bytes ending`: `events` are at most `r` reads of descriptor `fd`
after the bytes `done`, each into the window of `window` of the bytes before it, and `bytes` are
the bytes that they returned.  Each read but the last returned errno 0 and at least one byte.  The
last read returned no bytes (`eof`) or an errno (`failed`), or `r` reads returned bytes (`cut`). -/
inductive FileReads (fd : UInt64) : Nat → List UInt8 → List Event → List UInt8 → Ending → Prop
  | cut {done : List UInt8} : FileReads fd 0 done [] [] .cut
  | eof {r : Nat} {done : List UInt8} {outputs : List Bytes}
      (empty : returned (window done) outputs = []) :
      FileReads fd (r + 1) done [readEvent fd (window done) 0 outputs] [] .eof
  | failed {r : Nat} {done : List UInt8} {errno : UInt64} {outputs : List Bytes}
      (nonzero : errno ≠ 0) :
      FileReads fd (r + 1) done [readEvent fd (window done) errno outputs] [] (.failed errno)
  | more {r : Nat} {done : List UInt8} {outputs : List Bytes} {events : List Event}
      {bytes : List UInt8} {ending : Ending} (nonempty : returned (window done) outputs ≠ [])
      (rest : FileReads fd r (done ++ returned (window done) outputs) events bytes ending) :
      FileReads fd (r + 1) done (readEvent fd (window done) 0 outputs :: events)
        (returned (window done) outputs ++ bytes) ending

/-- The 64 hex digits of `hex` give the 32 bytes `d`, two digits to a byte, the high half first. -/
def HexDigits (hex : List UInt8) (d : Vector UInt8 32) : Prop :=
  ∀ k (hk : k < 32), hexValue (hex.getD (2 * k) 0) = some (d[k].toNat / 16) ∧
    hexValue (hex.getD (2 * k + 1) 0) = some (d[k].toNat % 16)

/-- The hex digits of `hex` give the SHA-256 digest of FIPS 180-4 of the bits of `bytes`, which
number fewer than `2^61` bytes. -/
def DigestOf (hex bytes : List UInt8) : Prop :=
  ∃ (d : Vector UInt8 32) (small : (bytesOf bytes).data.size < 2 ^ 61), HexDigits hex d ∧
    digestBitVec d = SHS.SHA256.sha256 (bytesToBitMessage (bytesOf bytes).data)
      (bitLen_lt_of_size_lt _ small)

/-- `FileCheck name line events ok`: `events` are those of the check of the line `line`, whose name
is `name`, and `ok` is its verdict.  An open that returns an errno ends the check with the verdict
false.  Otherwise the reads of `FileReads` follow, at most `2^45 - 1` of them, and the close of the
descriptor, and the verdict holds exactly when a read returned no bytes before any read returned an
errno, the close returned errno 0, and the line's digits give the digest of the bytes that the reads
returned. -/
inductive FileCheck (name line : List UInt8) : List Event → Bool → Prop
  | refused {errno : UInt64} {outputs : List Bytes} (nonzero : errno ≠ 0) :
      FileCheck name line [.sys .pathOpen (openArgs fileRights name) (.returned errno outputs)]
        false
  | opened {outputs : List Bytes} {events : List Event} {bytes : List UInt8} {ending : Ending}
      {closeErrno : UInt64} {committed : List Bytes} {ok : Bool}
      (reads : FileReads (openedDescriptor outputs) 35184372088831 [] events bytes ending)
      (verdict : ok = true ↔ ending = .eof ∧ closeErrno = 0 ∧ DigestOf line bytes) :
      FileCheck name line (.sys .pathOpen (openArgs fileRights name) (.returned 0 outputs) ::
        events ++ [.sys .fdClose [.word (openedDescriptor outputs)] (.returned closeErrno committed)])
        ok

/-- How the writes of an output line ended: every byte was taken, the writes stopped with bytes
left, or a write returned an errno. -/
inductive WriteEnd where
  | all
  | stalled
  | failed (errno : UInt64)
  deriving DecidableEq

/-- `LineWrites text writes ending`: `writes` are at most one more than the bytes of `text` writes
to standard output, each of which offered at least one byte, the bytes of `text` after those that
the writes before it took (`Offered`).  With `all`, each returned errno 0 and they took every byte
of `text`.  With `stalled`, each returned errno 0, they number one more than the bytes of `text`,
and the bytes that they took are a prefix of `text` that leaves bytes.  With `failed errno`, the
last returned the errno `errno`, from 1 to 76, each before it returned errno 0, and the bytes that
they took are a prefix of `text` that leaves bytes. -/
def LineWrites (text : List UInt8) (writes : List Event) (ending : WriteEnd) : Prop :=
  Offered text 0 writes ∧ writes.length ≤ text.length + 1 ∧ (∀ e ∈ writes, WroteSome e) ∧
    match ending with
    | .all => (∀ e ∈ writes, ∃ offered count, e = .write .stdout offered (.returned 0 count)) ∧
        stdoutTaken writes = text
    | .stalled => (∀ e ∈ writes, ∃ offered count, e = .write .stdout offered (.returned 0 count)) ∧
        writes.length = text.length + 1 ∧ stdoutTaken writes <+: text ∧
        (stdoutTaken writes).length < text.length
    | .failed errno => errno ≠ 0 ∧ errno.toNat ≤ 76 ∧
        (∃ before offered count,
          writes = before ++ [.write .stdout offered (.returned errno count)] ∧
          ∀ e ∈ before, ∃ offered count, e = .write .stdout offered (.returned 0 count)) ∧
        stdoutTaken writes <+: text ∧ (stdoutTaken writes).length < text.length

/-- The bytes of the output line of `name` with the verdict `ok`. -/
def lineText (name : List UInt8) (ok : Bool) : List UInt8 :=
  (renderSpec (bytesOf name, ok)).data.data.toList

/-- `Checks lines allOk events code`: `events` are those of the checks of the lines `lines`, after
lines whose verdicts were all OK exactly when `allOk` holds, and `code` is the status that ends
them.  Each check is that of `FileCheck` for the line and its name, the bytes after its first 66,
followed by the writes of its output line, `lineText`.  The status is 0 when every line said OK
and 1 otherwise after the writes of every line took every byte, 77 when the writes of a line
stalled, and the errno of a write that failed, which end the checks. -/
inductive Checks : List (List UInt8) → Bool → List Event → UInt64 → Prop
  | done {allOk : Bool} : Checks [] allOk [] (if allOk then 0 else 1)
  | line {line : List UInt8} {rest : List (List UInt8)} {allOk ok : Bool}
      {fileEvents writes restEvents : List Event} {code : UInt64}
      (check : FileCheck (line.drop 66) line fileEvents ok)
      (wrote : LineWrites (lineText (line.drop 66) ok) writes .all)
      (more : Checks rest (allOk && ok) restEvents code) :
      Checks (line :: rest) allOk (fileEvents ++ writes ++ restEvents) code
  | stalled {line : List UInt8} {rest : List (List UInt8)} {allOk ok : Bool}
      {fileEvents writes : List Event}
      (check : FileCheck (line.drop 66) line fileEvents ok)
      (wrote : LineWrites (lineText (line.drop 66) ok) writes .stalled) :
      Checks (line :: rest) allOk (fileEvents ++ writes) 77
  | failed {line : List UInt8} {rest : List (List UInt8)} {allOk ok : Bool}
      {fileEvents writes : List Event} {errno : UInt64}
      (check : FileCheck (line.drop 66) line fileEvents ok)
      (wrote : LineWrites (lineText (line.drop 66) ok) writes (.failed errno)) :
      Checks (line :: rest) allOk (fileEvents ++ writes) errno

/-- The verdicts and statuses of a run from `world` whose events before its exit are `events` and
whose status is `code`, under the host `host`: the events of `args`, which returned `a`, followed
by those of `ManifestRun` for the buffer's one argument, which gave the manifest's bytes `manifest`
with status 0, and then by those of `Checks` for its lines.  An errno of `args` is the status, and
a buffer without exactly one argument after the program name gives status 1, each with no other
event.  A status of `ManifestRun` other than 0 is the run's, and a manifest without a line or with
a line outside the format gives status 1, each with no other event. -/
def Run {World : Type} (host : Host World) (world : World) (a : ArgsResult)
    (manifest : List UInt8) (events : List Event) (code : UInt64) : Prop :=
  ∃ (pre rest : List Event) (middle : World),
    events = pre ++ rest ∧ Exec host args world pre (.returned a) middle ∧
    (a.errno ≠ 0 → code = a.errno ∧ rest = []) ∧
    (a.errno = 0 → (∀ name, ¬ OneArgument a.bytes.data.data.toList name) →
      code = 1 ∧ rest = []) ∧
    (a.errno = 0 → ∀ name, OneArgument a.bytes.data.data.toList name →
      ∃ opening post status, rest = opening ++ post ∧ ManifestRun name opening status manifest ∧
        (status ≠ 0 → code = status ∧ post = []) ∧
        (status = 0 → (lines manifest = [] ∨ ∃ l ∈ lines manifest, ¬ WellFormed l.2) →
          code = 1 ∧ post = []) ∧
        (status = 0 → lines manifest ≠ [] → (∀ l ∈ lines manifest, WellFormed l.2) →
          Checks ((lines manifest).map (·.2)) true post code))

/-- Confinement: every open of `events` is relative to descriptor 3, with the flag
`symlink_follow`, no open flags, the read-only rights `manifestRights` or `fileRights`, no inherited
rights, and no descriptor flags, and names the one argument of the argument buffer `buffer` with
the rights `manifestRights` or the name of a line of the manifest's bytes `manifest` in the
format, the bytes after its first 66, with the rights `fileRights`. -/
def Confined (buffer manifest : List UInt8) (events : List Event) : Prop :=
  ∀ args reply, Event.sys .pathOpen args reply ∈ events →
    ∃ name, (args = openArgs manifestRights name ∧ OneArgument buffer name) ∨
      (args = openArgs fileRights name ∧
        ∃ l ∈ lines manifest, WellFormed l.2 ∧ name = l.2.drop 66)

/-- The event `e` is a call on descriptor `fd`: a read or `fd_filestat_get`. -/
def OnDescriptor (fd : UInt64) (e : Event) : Prop :=
  (∃ length reply, e = .sys .fdRead [.word fd, .space length] reply) ∨
    ∃ reply, e = .sys .fdFilestatGet [.word fd] reply

/-- The use of descriptors: the events are calls of `args_sizes_get` and `args_get`, opens that
return an errno, opens that return errno 0 followed by calls on the opened descriptor and then its
close, and writes to standard output.  Each descriptor is closed before the next open and before
the end of the events, and no event writes to another descriptor. -/
inductive Handled : List Event → Prop
  | nil : Handled []
  | write {offered : Bytes} {reply : Transfer UInt64} {rest : List Event} (tail : Handled rest) :
      Handled (.write .stdout offered reply :: rest)
  | argsCall {call : Call} {args : List Arg} {reply : Transfer (List Bytes)} {rest : List Event}
      (named : call = .argsSizesGet ∨ call = .argsGet) (tail : Handled rest) :
      Handled (.sys call args reply :: rest)
  | refused {args : List Arg} {errno : UInt64} {outputs : List Bytes} {rest : List Event}
      (nonzero : errno ≠ 0) (tail : Handled rest) :
      Handled (.sys .pathOpen args (.returned errno outputs) :: rest)
  | bracket {args : List Arg} {outputs : List Bytes} {inner : List Event}
      {closed : Transfer (List Bytes)} {rest : List Event}
      (calls : ∀ e ∈ inner, OnDescriptor (openedDescriptor outputs) e) (tail : Handled rest) :
      Handled (.sys .pathOpen args (.returned 0 outputs) :: (inner ++
        .sys .fdClose [.word (openedDescriptor outputs)] closed :: rest))

/-- What the request asks of a run from `world` whose events before its exit are `events` and
whose status is `code`: the verdicts and statuses of `Run`, for the arguments `a` that `args`
returned and the bytes `manifest` of the manifest; confinement, every open naming the buffer's
argument or the name of a line of the manifest; and the use of descriptors of `Handled`. -/
def Meets {World : Type} (host : Host World) (world : World) (events : List Event)
    (code : UInt64) : Prop :=
  ∃ (a : ArgsResult) (manifest : List UInt8), Run host world a manifest events code ∧
    Confined a.bytes.data.data.toList manifest events ∧ Handled events

/-- The events at the end of a run that stopped without an accepted exit: none, an open that
returned errno 0 followed by calls on the descriptor that it opened and no close, an open that
trapped, or an exit that the host rejected. -/
inductive Unfinished : List Event → Prop
  | empty : Unfinished []
  | opened {args : List Arg} {outputs : List Bytes} {inner : List Event}
      (calls : ∀ e ∈ inner, OnDescriptor (openedDescriptor outputs) e) :
      Unfinished (.sys .pathOpen args (.returned 0 outputs) :: inner)
  | openTrapped {args : List Arg} {message : String} {committed : List Bytes} :
      Unfinished [.sys .pathOpen args (.trapped message committed)]
  | exitRejected {code : UInt64} {message : String} : Unfinished [.exitTrap code message]

/-- The use of descriptors of a run that stopped without an accepted exit: the events of `Handled`,
whose brackets are closed, followed by those of `Unfinished`. -/
def HandledSoFar (events : List Event) : Prop :=
  ∃ closed rest, events = closed ++ rest ∧ Handled closed ∧ Unfinished rest

/-- Confinement of the events `events` of a run from `world` that stopped without an accepted
exit: no event is an open, or the events start with those of a run of `args` that returned `a`,
and `Confined` holds of them for `a`'s buffer and the bytes `manifest`.  These are no bytes, or
the bytes of a `ManifestRun` with status 0 that follows the events of `args` and whose manifest
has at least one line and every line in the format, the manifest that the pure core accepts. -/
def ConfinedSoFar {World : Type} (host : Host World) (world : World) (events : List Event) :
    Prop :=
  (∀ arguments reply, Event.sys .pathOpen arguments reply ∉ events) ∨
    ∃ (a : ArgsResult) (pre rest : List Event) (middle : World) (manifest : List UInt8),
      events = pre ++ rest ∧ Exec host args world pre (.returned a) middle ∧
      (manifest = [] ∨ ∃ name opening post, rest = opening ++ post ∧
        ManifestRun name opening 0 manifest ∧ lines manifest ≠ [] ∧
        ∀ l ∈ lines manifest, WellFormed l.2) ∧
      Confined a.bytes.data.data.toList manifest events

/-- No event of `events` writes to standard output. -/
def Quiet (events : List Event) : Prop :=
  ∀ offered reply, Event.write .stdout offered reply ∉ events

/-- `ChecksSoFar lines events`: `events` are those of the checks of the first lines of `lines` in
order, each the events of `FileCheck` for the line and its name followed by the writes of its
output line with the verdict of `FileCheck`, which took every byte, as `Checks` states them.  They
are followed by no event, or by the events of `FileCheck` for the next line and writes of its
output line with that verdict, each of which offered at least one byte, the bytes of the output
line after those that the writes before it took. -/
inductive ChecksSoFar : List (List UInt8) → List Event → Prop
  | none {lines : List (List UInt8)} : ChecksSoFar lines []
  | line {line : List UInt8} {rest : List (List UInt8)} {ok : Bool}
      {fileEvents writes restEvents : List Event}
      (check : FileCheck (line.drop 66) line fileEvents ok)
      (wrote : LineWrites (lineText (line.drop 66) ok) writes .all)
      (more : ChecksSoFar rest restEvents) :
      ChecksSoFar (line :: rest) (fileEvents ++ writes ++ restEvents)
  | writing {line : List UInt8} {rest : List (List UInt8)} {ok : Bool}
      {fileEvents writes : List Event}
      (check : FileCheck (line.drop 66) line fileEvents ok)
      (offered : Offered (lineText (line.drop 66) ok) 0 writes)
      (some : ∀ e ∈ writes, WroteSome e) :
      ChecksSoFar (line :: rest) (fileEvents ++ writes)

/-- The verdicts of the events `events` of a run from `world` that stopped without an accepted
exit: no event writes to standard output, or the events are those of a run of `args` whose buffer
holds one argument, `name`, of a `ManifestRun` of `name` with status 0 whose manifest has at least
one line and every line in the format, of `ChecksSoFar` for the manifest's lines, and of events that
write nothing to standard output.  Every write to standard output therefore offers bytes of the
output line of a line of the manifest with the verdict of its `FileCheck`, which the digest of the
bytes that the host returned for the line's file decides. -/
def VerdictsSoFar {World : Type} (host : Host World) (world : World) (events : List Event) :
    Prop :=
  Quiet events ∨
    ∃ (a : ArgsResult) (pre : List Event) (middle : World) (name : List UInt8)
      (opening : List Event) (manifest : List UInt8) (checked tail : List Event),
      events = pre ++ opening ++ checked ++ tail ∧ Exec host args world pre (.returned a) middle ∧
      OneArgument a.bytes.data.data.toList name ∧ ManifestRun name opening 0 manifest ∧
      lines manifest ≠ [] ∧ (∀ l ∈ lines manifest, WellFormed l.2) ∧
      ChecksSoFar ((lines manifest).map (·.2)) checked ∧ Quiet tail

/-- The three properties of the events `events` of a run from `world` that stopped without an
accepted exit, at a trap of the host, at an exit that the host rejected, or at a trap of the guest:
confinement, `ConfinedSoFar`, the use of descriptors, `HandledSoFar`, and the verdicts,
`VerdictsSoFar`. -/
def SoFar {World : Type} (host : Host World) (world : World) (events : List Event) : Prop :=
  ConfinedSoFar host world events ∧ HandledSoFar events ∧ VerdictsSoFar host world events

end Demos.ManifestCheck
