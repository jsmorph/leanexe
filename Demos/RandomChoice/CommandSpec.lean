module

public import Demos.RandomChoice.Spec
public import Demos.RandomHistogram.CommandSpec
public import LeanExe.Wasi.Sys
public import Verified.Shim.Trace

@[expose] public section

/-! The specification of the runs of the unbiased random choice's WASI command, in terms of the
events of a run, `LeanExe.Wasi.Event`, which record each call with the reply that the host gave.

`accepted n ws` is the list of the picks of the accepted words of `ws`, in order, and `passPicks`
those that a pass with `r` values still to choose keeps, at most `r`.  `Writes` states the writes of
`writeAll`: each offers the bytes not yet written and returns an errno and the count of bytes that
it took.  `Rounds` states the passes of the loop: each calls `random_get` for 4,096 bytes, 512
little-endian words, and writes `renderSpec` of the pass's picks.  `Meets host world events code`
states what the request asks of a run from `world` whose events before its exit are `events` and
whose exit status is `code`.  The run starts with the events of a call of `args`, which returned
`a`.  An errno of `args` is the status, and no other event follows.  When `parseSpec` refuses
argument 1, N, or argument 2, K, the status is 2, and no other event follows.  Otherwise the events
are the passes of `Rounds` from K values and `passes K` passes.  The status is 0 exactly when the
passes chose K values and wrote them, and then the bytes written to standard output are
`renderSpec` of the first K picks of the accepted words that the passes drew.  A run whose passes
reach the cap ends with `capStatus`, after drawing `512 · passes K` words of which fewer than K are
accepted. -/

namespace Demos.RandomChoice

open LeanExe LeanExe.Wasi

/-- The picks of the accepted words of `ws` for the range [1, n], in order. -/
def accepted (n : UInt64) (ws : List UInt64) : List UInt64 :=
  (ws.map fun w => pickSpec (n, w)).filter (· != 0)

/-- The cap of the loop's passes for K values, each pass of 512 words: `K / 128 + 3`. -/
def passes (k : UInt64) : UInt64 := k / 128 + 3

/-- The status of a run whose passes reach the cap with values still to choose: 77, the least
status above the WASI errnos, 0 to 76. -/
def capStatus : UInt64 := 77

/-- The status of a run whose writes took fewer bytes than offered, with no errno, until the passes
of `writeAll` ran out: 78, the least status above `capStatus`. -/
def stalledStatus : UInt64 := 78

/-- The picks that a pass with `r` values still to choose keeps from the random bytes `buffer`: the
picks of the buffer's accepted words, at most `r` of them. -/
def passPicks (n r : UInt64) (buffer : Bytes) : List UInt64 :=
  (accepted n (RandomHistogram.words buffer.data.data.toList)).take r.toNat

/-- The bytes that a pass writes: the lines of its picks. -/
def passText (n r : UInt64) (buffer : Bytes) : List UInt8 :=
  (renderSpec (passPicks n r buffer).toArray).data.data.toList

/-- `Writes p text events status`: `events` are the writes to standard output that write the bytes
`text` with `p` passes left.  Each write offers the bytes not yet written.  The writes end when no
byte remains, with status 0, when no pass remains, with `stalledStatus`, or at a write that returns
an errno, at most 76, with that errno as the status. -/
inductive Writes : Nat → List UInt8 → List Event → UInt64 → Prop
  | done {p : Nat} : Writes p [] [] 0
  | stalled {text : List UInt8} (h : text ≠ []) : Writes 0 text [] stalledStatus
  | failed {p : Nat} {text : List UInt8} {offered : Bytes} {errno count : UInt64} (h : text ≠ [])
      (ho : offered.data.data.toList = text) (he : errno ≠ 0) (hb : errno.toNat ≤ 76) :
      Writes (p + 1) text [.write .stdout offered (.returned errno count)] errno
  | wrote {p : Nat} {text : List UInt8} {offered : Bytes} {count : UInt64} {events : List Event}
      {status : UInt64} (h : text ≠ []) (ho : offered.data.data.toList = text)
      (rest : Writes p (text.drop count.toNat) events status) :
      Writes (p + 1) text (.write .stdout offered (.returned 0 count) :: events) status

/-- `Rounds n r p events bytes status`: `events` are the passes of the loop from `r` values still to
choose with `p` passes left, `bytes` the random bytes that their calls of `random_get` returned, and
`status` the run's status after them.  A pass calls `random_get` for 4,096 bytes.  When the call
returns an errno, at most 76, that errno is the status.  Otherwise the pass writes `passText` with
`writeAll`, whose writes end the run with their status when it is not 0, and the next pass starts
with the values still to choose.  The passes end with status 0 when no value remains and with
`capStatus` when no pass remains. -/
inductive Rounds (n : UInt64) : UInt64 → Nat → List Event → List UInt8 → UInt64 → Prop
  | done {p : Nat} : Rounds n 0 p [] [] 0
  | capped {r : UInt64} (hr : r ≠ 0) : Rounds n r 0 [] [] capStatus
  | drawFailed {r : UInt64} {p : Nat} {errno : UInt64} {outputs : List Bytes} (hr : r ≠ 0)
      (he : errno ≠ 0) (hb : errno.toNat ≤ 76) :
      Rounds n r (p + 1) [.sys .randomGet [.space 4096] (.returned errno outputs)] [] errno
  | writeEnded {r : UInt64} {p : Nat} {buffer : Bytes} {writes : List Event} {status : UInt64}
      (hr : r ≠ 0) (hsize : buffer.data.size = 4096)
      (hw : Writes ((passText n r buffer).length + 1) (passText n r buffer) writes status)
      (hs : status ≠ 0) :
      Rounds n r (p + 1) (.sys .randomGet [.space 4096] (.returned 0 [buffer]) :: writes)
        buffer.data.data.toList status
  | drew {r : UInt64} {p : Nat} {buffer : Bytes} {writes events : List Event}
      {bytes : List UInt8} {status : UInt64} (hr : r ≠ 0) (hsize : buffer.data.size = 4096)
      (hw : Writes ((passText n r buffer).length + 1) (passText n r buffer) writes 0)
      (rest : Rounds n (r - UInt64.ofNat (passPicks n r buffer).length) p events bytes status) :
      Rounds n r (p + 1) (.sys .randomGet [.space 4096] (.returned 0 [buffer]) :: writes ++ events)
        (buffer.data.data.toList ++ bytes) status

/-- What the request asks of a run from `world` whose events before its exit are `events` and whose
status is `code`, for the host `host`, whose replies the events record. -/
def Meets {World : Type} (host : Host World) (world : World) (events : List Event) (code : UInt64) :
    Prop :=
  ∃ (a : ArgsResult) (pre rest : List Event) (middle : World),
    events = pre ++ rest ∧ Exec host args world pre (.returned a) middle ∧
    (a.errno ≠ 0 → code = a.errno ∧ rest = []) ∧
    (a.errno = 0 → (parseSpec (a.bytes, 1) = 0 ∨ parseSpec (a.bytes, 2) = 0) →
      code = 2 ∧ rest = []) ∧
    (a.errno = 0 → parseSpec (a.bytes, 1) ≠ 0 → parseSpec (a.bytes, 2) ≠ 0 → ∃ bytes,
      Rounds (parseSpec (a.bytes, 1)) (parseSpec (a.bytes, 2))
        (passes (parseSpec (a.bytes, 2))).toNat rest bytes code ∧
      (code = 0 →
        Verified.Shim.committedWrites 1 rest =
          (renderSpec ((accepted (parseSpec (a.bytes, 1)) (RandomHistogram.words bytes)).take
            (parseSpec (a.bytes, 2)).toNat).toArray).data.data.toList ∧
        (parseSpec (a.bytes, 2)).toNat ≤
          (accepted (parseSpec (a.bytes, 1)) (RandomHistogram.words bytes)).length) ∧
      (code = capStatus →
        (RandomHistogram.words bytes).length = 512 * (passes (parseSpec (a.bytes, 2))).toNat ∧
        (accepted (parseSpec (a.bytes, 1)) (RandomHistogram.words bytes)).length <
          (parseSpec (a.bytes, 2)).toNat))

end Demos.RandomChoice
