import LeanExe.Linux.CallTable

/-!
Properties of a kernel's replies that the frame rule of `LeanExe/Linux/Call.lean` does not state,
as predicates over a trace of events.  A theorem assumes only those that it needs, and each rests
on Linux 7.0's code, which the trusted base cites, and on the guard-page tests of
`tests/linux/sys-run.sh`.

- `FreshOpens`: a call that returns a descriptor returns an error or a number below 2^31 that is
  not open (`fs/file.c`, `alloc_fd`).  `openAfter` counts a descriptor closed by every `close` of
  it, whatever `close` returns, since `close` releases the descriptor before it flushes the file
  (`fs/open.c`, `SYSCALL_DEFINE1(close)`).
- `NsecBound`: a `clock_gettime` that returns 0 writes a `tv_nsec` below 10^9.
- `RandomCount`: a `getrandom` returns an error, or a count of at most its length that is
  positive for a positive length.
- `WrittenPrefix`: a `read` or `getrandom` whose result is at most its buffer's length changes
  only the first bytes of the buffer, as many as its result.

Linux reads a descriptor as the low 32 bits of its argument, and a result from 2^64 - 4095 to
2^64 - 1 is a negated error number.
-/

namespace LeanExe.Linux

/-- Whether a result is a negated error number, from -4095 to -1. -/
def isError (r : UInt64) : Bool := decide (2 ^ 64 - 4096 < r.toNat)

/-- The descriptor that a word names: its low 32 bits. -/
def descriptor (w : UInt64) : UInt64 := w &&& 0xFFFFFFFF

/-- The little-endian value of bytes. -/
def leValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leValue bs

/-- The descriptors open after the events `tr`, from the open descriptors `opened`: a result below
2^31 of a call that returns a descriptor opens that descriptor, and a `close` closes the
descriptor of its argument whatever it returns. -/
def openAfter : List UInt64 → List Event → List UInt64
  | opened, [] => opened
  | opened, e :: tr =>
    if e.call.opens = true ∧ e.ret.toNat < 2 ^ 31 then openAfter (e.ret :: opened) tr
    else if e.call = closeCall then
      openAfter (opened.filter (· ≠ descriptor (arg e.args 0))) tr
    else openAfter opened tr

/-- Every call of `tr` that returns a descriptor returns an error or a number below 2^31 that is
not open after the events before it, with `initial` open at the start. -/
def FreshOpens (initial : List UInt64) (tr : List Event) : Prop :=
  ∀ pre e post, tr = pre ++ e :: post → e.call.opens = true →
    isError e.ret = true ∨ (e.ret.toNat < 2 ^ 31 ∧ e.ret ∉ openAfter initial pre)

/-- Every `clock_gettime` of `tr` that returns 0 leaves a `tv_nsec` below 10^9 in its output. -/
def NsecBound (tr : List Event) : Prop :=
  ∀ e ∈ tr, e.call = clockGettimeCall → e.ret = 0 →
    leValue ((e.output.drop 8).take 8) < 10 ^ 9

/-- Every `getrandom` of `tr` returns an error, or a count of at most its length that is
positive for a positive length. -/
def RandomCount (tr : List Event) : Prop :=
  ∀ e ∈ tr, e.call = getrandomCall → isError e.ret = true ∨
    (e.ret.toNat ≤ (arg e.args 1).toNat ∧ ((arg e.args 1).toNat = 0 ∨ 0 < e.ret.toNat))

/-- Every `read` or `getrandom` of `tr` whose result is at most its buffer's length changes only
the first bytes of its buffer, as many as its result. -/
def WrittenPrefix (tr : List Event) : Prop :=
  ∀ e ∈ tr, (e.call = readCall ∨ e.call = getrandomCall) →
    e.ret.toNat ≤ e.output.length → e.output.drop e.ret.toNat = e.prior.drop e.ret.toNat

end LeanExe.Linux
