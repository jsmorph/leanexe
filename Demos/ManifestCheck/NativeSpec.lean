import Demos.ManifestCheck.CommandSpec
import Verified.Shim

/-! The specification of the native runs of the manifest checker in terms of the events of the
Linux call layer, `LeanExe.Linux.Event`, which record each call's arguments, the bytes of its input
regions, the bytes of its output region before and after the call, and its result.

`InRange ls` states that the result of each event of `ls` lies in the range that Linux gives for
its call: a `read` or a `write` returned an error number or at most its count, an `openat2` an
error number or a descriptor below 1,024, a `close` 0 or an error number, and a `statx` an error
number, or 0 with nanoseconds below `10^9` in each timestamp that `fd_filestat_get` reports.

`NMeets args ls code` states what the request asks of a run of the process with the arguments
`args`, each without its zero byte, whose layer events before `exit_group` are `ls` and whose status
is `code`.  It holds three properties.

- `NRun`, the verdicts and the status.  Arguments other than a program name and exactly one
  argument give status 1 and no event.  `NManifestRun` states the opening of the manifest that the
  argument names (`Opening`), the `statx` of its descriptor, the reads of its bytes, and its
  `close`, and the status that they give.  A manifest without a line, or with a line outside
  `sha256sum`'s format, gives status 1.  Otherwise `NChecks` states the check of each line in
  order: `NFileCheck`, the opening of its name, the reads of the file, its `close`, and its
  verdict, and then `NLineWrites`, the writes of its output line to descriptor 1.
- `NConfined`: every `openat2` is relative to descriptor 3, the preopened directory, with the flags
  `O_RDONLY | O_CLOEXEC` and the resolution `RESOLVE_BENEATH | RESOLVE_NO_MAGICLINKS`
  (`readOnlyHow`), and names the argument or the name of a line of an accepted manifest, one that
  has at least one line and every line in the format.
- `NHandled`: the events are `openat2` calls that returned an error number, brackets of an
  `openat2` that returned a descriptor, `read` and `statx` calls of that descriptor, and its
  `close`, and writes to descriptor 1.

A line's verdict is OK exactly when its opening returned a descriptor, a `read` returned 0 before
any `read` returned an error number, the `close` returned 0, and the line's digits give the digest
of FIPS 180-4 of the bytes that the reads returned (`DigestOf`).  An errno is the WASI errno of
the shim's reply: `errnoOf` of a negated error number. -/

namespace Demos.ManifestCheck

open LeanExe LeanExe.Wasi Verified.Shim

/-! ## The calls -/

/-- The result of every event of `ls` lies in the range that Linux gives for its call. -/
def InRange (ls : List Linux.Event) : Prop :=
  ∀ e ∈ ls,
    ((e.call = Linux.readCall ∨ e.call = Linux.writeCall) →
      Linux.isError e.ret = true ∨ e.ret.toNat ≤ (Linux.arg e.args 2).toNat) ∧
    (e.call = Linux.openat2Call → Linux.isError e.ret = true ∨ e.ret.toNat < 1024) ∧
    (e.call = Linux.closeCall → e.ret = 0 ∨ Linux.isError e.ret = true) ∧
    (e.call = Linux.statxCall → Linux.isError e.ret = true ∨
      (e.ret = 0 ∧ ∀ o ∈ stampOffsets e.output, stampValid e.output o = true))

/-- The `open_how` record of every open of the command: the flags `O_RDONLY | O_CLOEXEC`
(`0x80000`), the mode 0, and the resolution `RESOLVE_BENEATH | RESOLVE_NO_MAGICLINKS` (10), each as
eight little-endian bytes. -/
def readOnlyHow : List UInt8 :=
  [0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0]

/-- The event `e` is an `openat2` relative to descriptor 3 of `name`, which its input holds with a
zero byte, with the record `readOnlyHow`. -/
def OpensBeneath (name : List UInt8) (e : Linux.Event) : Prop :=
  e.call = Linux.openat2Call ∧ Linux.arg e.args 0 = 3 ∧ e.inputs = [name ++ [0], readOnlyHow]

/-- `Opening name opening errno fd`: `opening` are the events of an open of `name`, which gave the
errno `errno` and, for errno 0, the descriptor `fd`.  Either the open made no call and gave an errno
other than 0, or it made at most four `openat2` calls of `name` beneath descriptor 3, each but the
last of which returned `EAGAIN` (`2^64 − 11`), and the last returned a descriptor below 1,024,
which is `fd`, with errno 0, or an error number, whose errno is `errno`. -/
def Opening (name : List UInt8) (opening : List Linux.Event) (errno fd : UInt64) : Prop :=
  (opening = [] ∧ errno ≠ 0) ∨
    ∃ retries last, opening = retries ++ [last] ∧ retries.length ≤ 3 ∧
      (∀ e ∈ opening, OpensBeneath name e) ∧ (∀ e ∈ retries, e.ret = 0 - 11) ∧
      ((last.ret.toNat < 1024 ∧ errno = 0 ∧ fd = last.ret) ∨
        (Linux.isError last.ret = true ∧ errno = errnoOf (0 - last.ret)))

/-- The event `e` is a `read` of descriptor `fd` of `count` bytes. -/
def ReadOf (fd count : UInt64) (e : Linux.Event) : Prop :=
  e.call = Linux.readCall ∧ Linux.arg e.args 0 = fd ∧ Linux.arg e.args 2 = count

/-- The event `e` is the `statx` of descriptor `fd` with the empty path, `AT_EMPTY_PATH`, and the
mask `STATX_BASIC_STATS | STATX_BTIME`. -/
def StatOf (fd : UInt64) (e : Linux.Event) : Prop :=
  e.call = Linux.statxCall ∧ Linux.arg e.args 0 = fd ∧ e.inputs = [[0]] ∧
    Linux.arg e.args 2 = statxFlags ∧ Linux.arg e.args 3 = statxMask

/-- The event `e` is a `close` of descriptor `fd`. -/
def CloseOf (fd : UInt64) (e : Linux.Event) : Prop :=
  e.call = Linux.closeCall ∧ Linux.arg e.args 0 = fd

/-- The errno of a `close` that returned `ret`: 0 for 0 and `errnoOf` of a negated error number. -/
def closeErrno (ret : UInt64) : UInt64 := if ret = 0 then 0 else errnoOf (0 - ret)

/-- A timestamp that `fd_filestat_get` reports from the `statx` record `output` reaches `2^64`
nanoseconds, as each time before 1970 does. -/
def Overflows (output : List UInt8) : Prop := ∃ o ∈ stampOffsets output, 2 ^ 64 ≤ stampTime output o

/-- The size that the `statx` record `output` reports, `stx_size`. -/
def statxSize (output : List UInt8) : Nat := fieldAt output 40 8

/-! ## The manifest -/

/-- `NManifestReads fd size held events bytes status`: `events` are the reads of descriptor `fd`
for a buffer of `size` bytes after the bytes `held`, each of the bytes that follow those already
read, and `bytes` are `held` followed by the bytes that they returned.  Each read but the last
returned at least one byte.  The reads end with status 0 when the bytes fill the buffer, 1 when a
read returned 0 before the bytes filled the buffer, and the errno of a read that returned an error
number. -/
inductive NManifestReads (fd : UInt64) (size : Nat) :
    List UInt8 → List Linux.Event → List UInt8 → UInt64 → Prop
  | full {held : List UInt8} (filled : held.length = size) : NManifestReads fd size held [] held 0
  | short {held : List UInt8} {e : Linux.Event} (left : held.length < size)
      (read : ReadOf fd (UInt64.ofNat (size - held.length)) e) (zero : e.ret = 0) :
      NManifestReads fd size held [e] held 1
  | failed {held : List UInt8} {e : Linux.Event} (left : held.length < size)
      (read : ReadOf fd (UInt64.ofNat (size - held.length)) e)
      (error : Linux.isError e.ret = true) :
      NManifestReads fd size held [e] held (errnoOf (0 - e.ret))
  | more {held : List UInt8} {e : Linux.Event} {events : List Linux.Event} {bytes : List UInt8}
      {status : UInt64} (left : held.length < size)
      (read : ReadOf fd (UInt64.ofNat (size - held.length)) e) (positive : 0 < e.ret.toNat)
      (rest : NManifestReads fd size (held ++ e.readBytes fd) events bytes status) :
      NManifestReads fd size held (e :: events) bytes status

/-- `NManifestBody fd events status bytes`: `events` are those of the reading of the manifest open
at descriptor `fd`, `status` is its status, and, when the status is 0, `bytes` are the manifest's
bytes.  The `statx` comes first: an error number ends the reading with its errno, and a timestamp
of `2^64` nanoseconds or more, or a size of `2^32` bytes or more, ends it with status 61
(`overflow`).  Otherwise the reads of `NManifestReads` follow for a buffer of the size that it
reported, and a status other than 0 ends the reading.  When the bytes fill the buffer, a last read
of 65,536 bytes follows, and the status is its errno for an error number, 1 when it returned bytes,
and 0 when it returned 0. -/
inductive NManifestBody (fd : UInt64) : List Linux.Event → UInt64 → List UInt8 → Prop
  | statFailed {e : Linux.Event} (stat : StatOf fd e) (error : Linux.isError e.ret = true) :
      NManifestBody fd [e] (errnoOf (0 - e.ret)) []
  | overflow {e : Linux.Event} (stat : StatOf fd e) (zero : e.ret = 0)
      (beyond : Overflows e.output) :
      NManifestBody fd [e] 61 []
  | tooLarge {e : Linux.Event} (stat : StatOf fd e) (zero : e.ret = 0)
      (fits : ¬ Overflows e.output) (large : 2 ^ 32 ≤ statxSize e.output) :
      NManifestBody fd [e] 61 []
  | stopped {e : Linux.Event} {events : List Linux.Event} {held : List UInt8} {status : UInt64}
      (stat : StatOf fd e) (zero : e.ret = 0) (fits : ¬ Overflows e.output)
      (small : statxSize e.output < 2 ^ 32)
      (reads : NManifestReads fd (statxSize e.output) [] events held status)
      (nonzero : status ≠ 0) :
      NManifestBody fd (e :: events) status []
  | probed {e last : Linux.Event} {events : List Linux.Event} {bytes : List UInt8}
      (stat : StatOf fd e) (zero : e.ret = 0) (fits : ¬ Overflows e.output)
      (small : statxSize e.output < 2 ^ 32)
      (reads : NManifestReads fd (statxSize e.output) [] events bytes 0)
      (probe : ReadOf fd 65536 last) :
      NManifestBody fd (e :: events ++ [last])
        (if Linux.isError last.ret then errnoOf (0 - last.ret) else if last.ret ≠ 0 then 1 else 0)
        bytes

/-- `NManifestRun name events status bytes`: `events` are those of the opening of the manifest
`name`, its reading, and its `close`, `status` is their status, and, when the status is 0, `bytes`
are the manifest's bytes.  An opening that gives an errno ends with that errno.  Otherwise the
events of `NManifestBody` follow on the descriptor, and its `close`, and the status is that of the
body when it is not 0, and else the errno of the `close`. -/
inductive NManifestRun (name : List UInt8) : List Linux.Event → UInt64 → List UInt8 → Prop
  | refused {opening : List Linux.Event} {errno : UInt64} (opened : Opening name opening errno 0)
      (nonzero : errno ≠ 0) : NManifestRun name opening errno []
  | opened {opening body : List Linux.Event} {fd status : UInt64} {bytes : List UInt8}
      {close : Linux.Event} (opened : Opening name opening 0 fd)
      (reading : NManifestBody fd body status bytes) (closed : CloseOf fd close) :
      NManifestRun name (opening ++ body ++ [close])
        (if status ≠ 0 then status else closeErrno close.ret) bytes

/-! ## The checks -/

/-- `NFileReads fd r done events bytes ending`: `events` are at most `r` reads of descriptor `fd`
after the bytes `done`, each of `window done` bytes, the bytes of the read buffer of 65,536 bytes
after those that it holds, and `bytes` are the bytes that they returned.  Each read but the last
returned at least one byte.  The last returned 0 (`eof`) or an error number (`failed`), or `r` reads
returned bytes (`cut`). -/
inductive NFileReads (fd : UInt64) : Nat → List UInt8 → List Linux.Event → List UInt8 → Ending →
    Prop
  | cut {done : List UInt8} : NFileReads fd 0 done [] [] .cut
  | eof {r : Nat} {done : List UInt8} {e : Linux.Event} (read : ReadOf fd (window done) e)
      (zero : e.ret = 0) : NFileReads fd (r + 1) done [e] [] .eof
  | failed {r : Nat} {done : List UInt8} {e : Linux.Event} (read : ReadOf fd (window done) e)
      (error : Linux.isError e.ret = true) :
      NFileReads fd (r + 1) done [e] [] (.failed (errnoOf (0 - e.ret)))
  | more {r : Nat} {done : List UInt8} {e : Linux.Event} {events : List Linux.Event}
      {bytes : List UInt8} {ending : Ending} (read : ReadOf fd (window done) e)
      (positive : 0 < e.ret.toNat)
      (rest : NFileReads fd r (done ++ e.readBytes fd) events bytes ending) :
      NFileReads fd (r + 1) done (e :: events) (e.readBytes fd ++ bytes) ending

/-- `NFileCheck name line events ok`: `events` are those of the check of the line `line`, whose
name is `name`, and `ok` is its verdict.  An opening that gives an errno ends the check with the
verdict false.  Otherwise the reads of `NFileReads` follow, at most `2^45 − 1` of them, and the
`close` of the descriptor, and the verdict holds exactly when a read returned 0 before any read
returned an error number, the `close` returned 0, and the line's digits give the digest of the
bytes that the reads returned. -/
inductive NFileCheck (name line : List UInt8) : List Linux.Event → Bool → Prop
  | refused {opening : List Linux.Event} {errno : UInt64} (opened : Opening name opening errno 0)
      (nonzero : errno ≠ 0) : NFileCheck name line opening false
  | opened {opening events : List Linux.Event} {fd : UInt64} {bytes : List UInt8}
      {ending : Ending} {close : Linux.Event} {ok : Bool} (opened : Opening name opening 0 fd)
      (reads : NFileReads fd 35184372088831 [] events bytes ending) (closed : CloseOf fd close)
      (verdict : ok = true ↔ ending = .eof ∧ close.ret = 0 ∧ DigestOf line bytes) :
      NFileCheck name line (opening ++ events ++ [close]) ok

/-- `NLineWrites text writes ending`: `writes` are at most one more than the bytes of `text` writes
to descriptor 1, each of which offered at least one byte, the bytes of `text` after those that the
writes before it took.  With `all`, none returned an error number and they took every byte of
`text`.  With `stalled`, none returned an error number, they number one more than the bytes of
`text`, and the bytes that they took are a prefix of `text` that leaves bytes.  With
`failed errno`, the last returned an error number whose errno is `errno`, none before it returned
one, and the bytes that they took are a prefix of `text` that leaves bytes. -/
def NLineWrites (text : List UInt8) (writes : List Linux.Event) (ending : WriteEnd) : Prop :=
  (∀ i (h : i < writes.length),
    writes[i].inputs.headD [] = text.drop (Linux.writeData 1 (writes.take i)).length) ∧
  (∀ e ∈ writes, e.call = Linux.writeCall ∧ Linux.arg e.args 0 = 1 ∧ e.inputs.headD [] ≠ []) ∧
  writes.length ≤ text.length + 1 ∧
    match ending with
    | .all => (∀ e ∈ writes, Linux.isError e.ret = false) ∧ Linux.writeData 1 writes = text
    | .stalled => (∀ e ∈ writes, Linux.isError e.ret = false) ∧
        writes.length = text.length + 1 ∧ Linux.writeData 1 writes <+: text ∧
        (Linux.writeData 1 writes).length < text.length
    | .failed errno => (∃ before e, writes = before ++ [e] ∧
          (∀ x ∈ before, Linux.isError x.ret = false) ∧ Linux.isError e.ret = true ∧
          errno = errnoOf (0 - e.ret)) ∧
        Linux.writeData 1 writes <+: text ∧ (Linux.writeData 1 writes).length < text.length

/-- `NChecks lines allOk events code`: `events` are those of the checks of the lines `lines`, after
lines whose verdicts were all OK exactly when `allOk` holds, and `code` is the status that ends
them.  Each check is that of `NFileCheck` for the line and its name, the bytes after its first 66,
followed by the writes of its output line, `lineText`.  The status is 0 when every line said OK and
1 otherwise after the writes of every line took every byte, 77 when the writes of a line stalled,
and the errno of a write that returned an error number, which end the checks. -/
inductive NChecks : List (List UInt8) → Bool → List Linux.Event → UInt64 → Prop
  | done {allOk : Bool} : NChecks [] allOk [] (if allOk then 0 else 1)
  | line {line : List UInt8} {rest : List (List UInt8)} {allOk ok : Bool}
      {fileEvents writes restEvents : List Linux.Event} {code : UInt64}
      (check : NFileCheck (line.drop 66) line fileEvents ok)
      (wrote : NLineWrites (lineText (line.drop 66) ok) writes .all)
      (more : NChecks rest (allOk && ok) restEvents code) :
      NChecks (line :: rest) allOk (fileEvents ++ writes ++ restEvents) code
  | stalled {line : List UInt8} {rest : List (List UInt8)} {allOk ok : Bool}
      {fileEvents writes : List Linux.Event}
      (check : NFileCheck (line.drop 66) line fileEvents ok)
      (wrote : NLineWrites (lineText (line.drop 66) ok) writes .stalled) :
      NChecks (line :: rest) allOk (fileEvents ++ writes) 77
  | failed {line : List UInt8} {rest : List (List UInt8)} {allOk ok : Bool}
      {fileEvents writes : List Linux.Event} {errno : UInt64}
      (check : NFileCheck (line.drop 66) line fileEvents ok)
      (wrote : NLineWrites (lineText (line.drop 66) ok) writes (.failed errno)) :
      NChecks (line :: rest) allOk (fileEvents ++ writes) errno

/-! ## The run -/

/-- The verdicts and statuses of a run with the arguments `args` whose layer events before
`exit_group` are `events` and whose status is `code`, with `manifest` the manifest's bytes.
Arguments other than a program name and one argument give status 1 and no event.  For the
argument `name`, the events start with those of `NManifestRun` for `name`, whose status, when it is
not 0, is the run's, with no other event.  A manifest without a line or with a line outside the
format gives status 1 and no other event.  Otherwise the events of `NChecks` for its lines
follow. -/
def NRun (args : List (List UInt8)) (manifest : List UInt8) (events : List Linux.Event)
    (code : UInt64) : Prop :=
  (args.length ≠ 2 → code = 1 ∧ events = []) ∧
  ∀ program name, args = [program, name] →
    ∃ opening post status, events = opening ++ post ∧ NManifestRun name opening status manifest ∧
      (status ≠ 0 → code = status ∧ post = []) ∧
      (status = 0 → (lines manifest = [] ∨ ∃ l ∈ lines manifest, ¬ WellFormed l.2) →
        code = 1 ∧ post = []) ∧
      (status = 0 → lines manifest ≠ [] → (∀ l ∈ lines manifest, WellFormed l.2) →
        NChecks ((lines manifest).map (·.2)) true post code)

/-- Confinement: every `openat2` of `events` is relative to descriptor 3, with the record
`readOnlyHow`, and names the argument of `args` or the name of a line of the manifest's bytes
`manifest`, the bytes after its first 66, when the manifest has at least one line and every line
in the format. -/
def NConfined (args : List (List UInt8)) (manifest : List UInt8) (events : List Linux.Event) :
    Prop :=
  ∀ e ∈ events, e.call = Linux.openat2Call →
    ∃ name, OpensBeneath name e ∧ ((∃ program, args = [program, name]) ∨
      (lines manifest ≠ [] ∧ (∀ l ∈ lines manifest, WellFormed l.2) ∧
        ∃ l ∈ lines manifest, name = l.2.drop 66))

/-- The use of descriptors: the events are `openat2` calls that returned an error number,
`openat2` calls that returned a descriptor below 1,024 followed by `read` and `statx` calls of that
descriptor and then its `close`, and writes to descriptor 1.  Each descriptor is closed before the
next `openat2` and before the end of the events, and no event writes to another descriptor. -/
inductive NHandled : List Linux.Event → Prop
  | nil : NHandled []
  | write {e : Linux.Event} {rest : List Linux.Event} (write : e.call = Linux.writeCall)
      (stdout : Linux.arg e.args 0 = 1) (tail : NHandled rest) : NHandled (e :: rest)
  | refused {e : Linux.Event} {rest : List Linux.Event} (opens : e.call = Linux.openat2Call)
      (error : Linux.isError e.ret = true) (tail : NHandled rest) : NHandled (e :: rest)
  | bracket {e close : Linux.Event} {inner rest : List Linux.Event}
      (opens : e.call = Linux.openat2Call) (opened : e.ret.toNat < 1024)
      (calls : ∀ x ∈ inner, (x.call = Linux.readCall ∨ x.call = Linux.statxCall) ∧
        Linux.arg x.args 0 = e.ret)
      (closed : CloseOf e.ret close) (tail : NHandled rest) :
      NHandled (e :: (inner ++ close :: rest))

/-- What the request asks of a native run with the arguments `args` whose layer events before
`exit_group` are `events` and whose status is `code`: the verdicts and statuses of `NRun` for the
manifest's bytes `manifest`, confinement, every `openat2` beneath descriptor 3 naming the argument
or the name of a line of an accepted manifest, and the use of descriptors of `NHandled`. -/
def NMeets (args : List (List UInt8)) (events : List Linux.Event) (code : UInt64) : Prop :=
  ∃ manifest, NRun args manifest events code ∧ NConfined args manifest events ∧ NHandled events

end Demos.ManifestCheck
