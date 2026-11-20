import Demos.RandomHistogram.Spec
import LeanExe.Wasi.Sys
import LeanExe.Wasi.Semantics
import LeanExe.Wasi.WriteAll

/-! The specification of the runs of the random-residue histogram's WASI command, in terms of the
events of a run, `LeanExe.Wasi.Event`, which record each call with the reply that the host gave.

`words` reads random bytes as the request's random numbers: 64-bit little-endian words.  `Draws`
states the calls of `random_get` of a run that draws `r` words, at most 512 a call, and the bytes
that they returned.  `Written out writes code` states the writes of the output `out` and the status
`code`.  `Meets host world events code` states what the request asks of a run from `world` whose
events before its exit are `events` and whose exit status is `code`.  The run starts with the
events of a call of `args`, which returned `a`.  An errno of `args` is the status, and no other
event follows.  When `parseSpec` refuses the argument buffer, the status is 2, and no other event
follows.  Otherwise the run draws `N = parseSpec a.bytes` words.  A call of `random_get` that
returns an errno ends the run with that errno as the status and no write.  When every call returns
errno 0, the bytes hold exactly N words `w`, the counts of `histogramSpec w` sum to N, and the
writes and the status meet `Written` for the output `renderSpec (histogramSpec w)`. -/

namespace Demos.RandomHistogram

open LeanExe LeanExe.Wasi

/-- The value of the little-endian bytes `bs`, the first the least significant. -/
def leValue (bs : List UInt8) : Nat := bs.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- The 64-bit little-endian words of `bytes`: word `j` is the value of bytes `8 j` to `8 j + 7`.
Bytes after the last whole word give no word. -/
def words (bytes : List UInt8) : List UInt64 :=
  (List.range (bytes.length / 8)).map fun j => UInt64.ofNat (leValue ((bytes.drop (8 * j)).take 8))

/-- `Draws r events bytes errno`: `events` are the calls of `random_get` that draw `r` words, each
call for `8 · min r' 512` bytes with `r'` the words still to draw.  Each call but the last returns
errno 0 and a buffer of the size asked for, whose bytes `bytes` collects.  Either every call
returns errno 0 and the calls end when no word remains, with `errno = 0`, or the last call returns
the errno `errno ≠ 0`. -/
inductive Draws : UInt64 → List Event → List UInt8 → UInt64 → Prop
  | done : Draws 0 [] [] 0
  | failed {r errno : UInt64} {outputs : List Bytes} (hr : r ≠ 0) (he : errno ≠ 0) :
      Draws r [.sys .randomGet [.space (8 * min r 512)] (.returned errno outputs)] [] errno
  | drew {r errno : UInt64} {buffer : Bytes} {events : List Event} {bytes : List UInt8}
      (hr : r ≠ 0) (hsize : buffer.data.size = 8 * min r.toNat 512)
      (rest : Draws (r - min r 512) events bytes errno) :
      Draws r (.sys .randomGet [.space (8 * min r 512)] (.returned 0 [buffer]) :: events)
        (buffer.data.data.toList ++ bytes) errno

/-- `Written out writes code`: the events `writes` are at most `out.length + 1` writes to stdout,
one for each of the loop's passes at most, each of which offered at least one byte (`WroteSome`),
the bytes of `out` after those that the writes before it took (`Offered`), and the bytes that they
took, `stdoutTaken writes`, form a prefix of `out`.  The status `code` is 0 exactly when that prefix
is all of `out`.  Either every write returned errno 0 and the status is 0, or 77 after one write for
each of the loop's `out.length + 1` passes, or the last write returned the errno `code`, from 1 to
76, and every write before it returned errno 0. -/
def Written (out : List UInt8) (writes : List Event) (code : UInt64) : Prop :=
  Offered out 0 writes ∧ writes.length ≤ out.length + 1 ∧ (∀ e ∈ writes, WroteSome e) ∧
    stdoutTaken writes <+: out ∧ (code = 0 ↔ stdoutTaken writes = out) ∧
    (((∀ e ∈ writes, ∃ offered count, e = .write .stdout offered (.returned 0 count)) ∧
        (code = 0 ∨ (code = 77 ∧ writes.length = out.length + 1))) ∨
      (code ≠ 0 ∧ code.toNat ≤ 76 ∧ ∃ before offered count,
        writes = before ++ [.write .stdout offered (.returned code count)] ∧
        ∀ e ∈ before, ∃ offered count, e = .write .stdout offered (.returned 0 count)))

/-- What the request asks of a run from `world` whose events before its exit are `events` and whose
status is `code`, for the host `host`, whose replies the events record. -/
def Meets {World : Type} (host : Host World) (world : World) (events : List Event) (code : UInt64) :
    Prop :=
  ∃ (a : ArgsResult) (pre rest : List Event) (middle : World),
    events = pre ++ rest ∧ Exec host args world pre (.returned a) middle ∧
    (a.errno ≠ 0 → code = a.errno ∧ rest = []) ∧
    (a.errno = 0 → parseSpec a.bytes = 0 → code = 2 ∧ rest = []) ∧
    (a.errno = 0 → parseSpec a.bytes ≠ 0 → ∃ draws bytes errno writes,
      rest = draws ++ writes ∧ Draws (parseSpec a.bytes) draws bytes errno ∧
      (errno ≠ 0 → code = errno ∧ writes = []) ∧
      (errno = 0 → (words bytes).length = (parseSpec a.bytes).toNat ∧
        ((histogramSpec (words bytes).toArray).toList.map UInt64.toNat).sum =
          (parseSpec a.bytes).toNat ∧
        Written (renderSpec (histogramSpec (words bytes).toArray)).data.data.toList writes code))

end Demos.RandomHistogram
