module

public import Demos.OrderBook.Program
public import LeanExe.Dialect.Bytes
public import LeanExe.Wasi.Process

@[expose] public section

/-! The order book as a WASI process over stdin and stdout.  The process reads command records as
little-endian 64-bit words, seven words to a record, in reads of at most 4,096 bytes.  It runs the
whole records of each read through `Program.run` from the book that the earlier reads left, and it
writes the event words in the same form before it reads again.  Bytes that complete no record stay
in the carry until the next read.  At EOF the whole words of the carry, at most six, are passed to
`Program.run` as one short record, which the book rejects as malformed, and the process stops with
status 28 when bytes that fill no word remain and with status 0 otherwise.  A read or a write that
returns an errno stops the process with that errno. -/

namespace Demos.OrderBook.Process

open LeanExe LeanExe.Wasi

/-- The book's arrays, next id, and count, as in `Program.Book`; the carry, which holds the bytes
read but not yet in a whole record, or after EOF the bytes in no whole word; the event bytes of the
last batch and the number of them written; and whether a read has reported EOF. -/
structure State where
  oid : Array UInt64
  acct : Array UInt64
  qty : Array UInt64
  lvl : Array UInt64
  nxt : Array UInt64
  head : Array UInt64
  tail : Array UInt64
  nextId : UInt64
  count : UInt64
  carry : Bytes
  output : Bytes
  written : UInt64
  eof : Bool

/-- The empty book, built as `Program.init` builds it, with no carry and no output. -/
def initial : State :=
  ⟨LeanExe.build (Program.slots + 1) fun _ => 0, LeanExe.build (Program.slots + 1) fun _ => 0,
    LeanExe.build (Program.slots + 1) fun _ => 0, LeanExe.build (Program.slots + 1) fun _ => 0,
    LeanExe.build (Program.slots + 1) fun _ => 0, LeanExe.build 2048 fun _ => 0,
    LeanExe.build 2048 fun _ => 0, 1, 0, Bytes.empty, Bytes.empty, 0, false⟩

/-- Byte `i` of the bytes of `carry` followed by those of `input`, or 0 past their end. -/
@[inline] def byteAt (carry input : Bytes) (i : UInt64) : UInt64 :=
  if i < carry.size then carry.get i else input.get (i - carry.size)

/-- The first `count` words of the bytes of `carry` followed by those of `input`, each from eight
bytes, least significant byte first. -/
def wordsOf (carry input : Bytes) (count : UInt64) : Array UInt64 :=
  LeanExe.build count fun j =>
    LeanExe.loop 8 0 fun k w => w ||| (byteAt carry input (8 * j + k) <<< (8 * k))

/-- The eight bytes of each word of `words`, least significant byte first. -/
def eventBytes (words : Array UInt64) : Bytes :=
  Bytes.build (8 * words.size.toUInt64) fun i => words[(i / 8).toNat]! >>> (8 * (i % 8))

/-- The bytes of `carry` followed by the first `used` bytes of `input`, from byte `start` on. -/
def tailBytes (carry input : Bytes) (used start : UInt64) : Bytes :=
  Bytes.build (carry.size + used - start) fun i => byteAt carry input (start + i)

/-- The first `count` words of the carry followed by the first `used` bytes of `input`, through
the book, with the bytes after them as the carry, their event bytes as the output, and `eof` as the
EOF flag. -/
def runWords (s : State) (input : Bytes) (used count : UInt64) (eof : Bool) : ProcessStep State :=
  let r := Program.run s.oid s.acct s.qty s.lvl s.nxt s.head s.tail s.nextId s.count
    (wordsOf s.carry input count)
  ⟨true, 0, ⟨r.1.oid, r.1.acct, r.1.qty, r.1.lvl, r.1.nxt, r.1.head, r.1.tail, r.1.nextId,
    r.1.count, tailBytes s.carry input used (8 * count), eventBytes r.2, 0, eof⟩⟩

/-- The bytes of the output that remain to be written: the window of the output from `written`
to its end, which `writeStep` writes in place. -/
def remainingOutput (s : State) : Bytes :=
  s.output.range s.written (s.output.size - s.written)

/-- The step after a write that returned `reply`: an errno stops the process with it, a write that
completes the output clears it, and a shorter write advances `written`. -/
def afterWrite (s : State) (reply : WriteResult) : ProcessStep State :=
  if reply.errno != 0 then ⟨false, reply.errno, s⟩
  else if s.written + reply.count == s.output.size then
    ⟨true, 0, { s with output := Bytes.empty, written := 0 }⟩
  else ⟨true, 0, { s with written := s.written + reply.count }⟩

/-- The step after a read into a buffer that returned `reply`: an errno stops the process with it,
an empty read runs the whole words of the carry at EOF, and other bytes, the first `reply.count`
bytes of the buffer, run the whole records of the carry followed by them. -/
def afterRead (s : State) (reply : FillResult) : ProcessStep State :=
  if reply.errno != 0 then ⟨false, reply.errno, s⟩
  else if reply.count == 0 then runWords s reply.buffer 0 (s.carry.size / 8) true
  else runWords s reply.buffer reply.count (7 * ((s.carry.size + reply.count) / 56)) false

def writeStep (s : State) : Action (ProcessStep State) := do
  let reply ← writeStdout s.output s.written (s.output.size - s.written)
  pure (afterWrite s reply)

def readStep (s : State) : Action (ProcessStep State) := do
  let reply ← readStdin (Bytes.build 4096 fun _ => 0) 0 4096
  pure (afterRead s reply)

/-- One step: a write while output remains, otherwise after EOF a stop with status 0 when the carry
is empty and 28 when it holds bytes that fill no word, and otherwise a read. -/
def step (s : State) : Action (ProcessStep State) :=
  if s.written < s.output.size then writeStep s
  else if s.eof then pure ⟨false, if s.carry.size == 0 then 0 else 28, s⟩
  else readStep s

def begin : Action (ProcessStep State) := pure ⟨true, 0, initial⟩

def process : Process State := ⟨initial, step⟩

end Demos.OrderBook.Process
