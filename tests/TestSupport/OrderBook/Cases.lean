import Demos.OrderBook.Program
import TestSupport.OrderBook.Edges
import TestSupport.OrderBook.Words
import Library.Random.SplitMix64.Program

/-! The cases of the module `orderbook`: the export `run` on the samples, the single records, the
edge streams, and random streams that SplitMix64 draws from fixed seeds, from the empty book and
from the books that the first part of a stream leaves, and the export `top` on each book that
`run` returns, with native Lean's results.  Every array of a case passes through a file of
little-endian words under `build/verified/orderbook/`, which `cases` writes, since a book's arrays
and the long streams exceed the length of a command-line argument.

A case of `run` requires nine retained blocks, the seven arrays of the returned book, its event
array, and the host's stream, and at most `9 + ⌊log₂ n⌋ + 1` allocations for `n` event words: the
host's eight arrays, the empty event array, and one block for each doubling of its capacity.  A
copy of a book array in every step would exceed that count on any stream of more than a few
records.  A case of `top` requires the host's seven arrays retained and no allocation of its own. -/

namespace TestSupport.OrderBook.Cases

open Demos.OrderBook
open TestSupport.OrderBook.Words (wordBytes hostArray)

/-- The directory of the cases' files, relative to the repository's root. -/
def dir : System.FilePath := "build/verified/orderbook"

/-- The result kinds of `run`: the book's seven arrays, its next id, its count, and the event
words. -/
def runKinds : String :=
  "list:" ++ ",".intercalate (List.replicate 7 "array-u64" ++ ["i64", "i64", "array-u64"])

/-- The arrays of a book, each with its field's name. -/
def arrays (b : Program.Book) : List (String × Array UInt64) :=
  [("oid", b.oid), ("acct", b.acct), ("qty", b.qty), ("lvl", b.lvl), ("nxt", b.nxt),
    ("head", b.head), ("tail", b.tail)]

/-- `run` from the book `b` on the stream `ws`. -/
def runFrom (b : Program.Book) (ws : Array UInt64) : Program.Book × Array UInt64 :=
  Program.run b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count ws

/-- The host's arguments for the book `b`, one file for each array, which it writes under a name
that begins with `name`, then the next id and the count. -/
def bookArgs (name : String) (b : Program.Book) : IO String := do
  let mut args := #[]
  for (field, xs) in arrays b do
    let path := dir / s!"{name}.{field}.bin"
    IO.FS.writeBinFile path (wordBytes xs)
    args := args.push s!"file-u64:{path}"
  return " ".intercalate (args.toList ++ [s!"i64:{b.nextId}", s!"i64:{b.count}"])

/-- The most allocations of a call of `run` whose events take `n` words. -/
def runAllocs (n : Nat) : Nat := 9 + if n = 0 then 0 else n.log2 + 1

/-- Prints the case of `run` from the book `b` on the stream `ws` and the case of `top` on the book
that `run` returns. -/
def emit (name : String) (b : Program.Book) (ws : Array UInt64) : IO Unit := do
  let input ← bookArgs name b
  let stream := dir / s!"{name}.stream.bin"
  IO.FS.writeBinFile stream (wordBytes ws)
  let (b', out) := runFrom b ws
  let expected := " ".intercalate ((arrays b').map (hostArray ·.2) ++
    [toString b'.nextId, toString b'.count, hostArray out])
  IO.println
    s!"orderbook|run|{runKinds}|{input} file-u64:{stream}|{expected}|9|{runAllocs out.size}"
  let after ← bookArgs s!"{name}.after" b'
  let (bp, bq, ap, aq) := Program.top b'
  IO.println s!"orderbook|top|list:i64,i64,i64,i64|{after}|{bp} {bq} {ap} {aq}|7|7"

/-- Prints the case of `run` on the records of `ws` after the first `k`, from the book that the
first `k` leave from `b`. -/
def emitRest (name : String) (b : Program.Book) (ws : Array UInt64) (k : Nat) : IO Unit :=
  emit s!"{name}-from-{k}" (runFrom b (ws.extract 0 (7 * k))).1 (ws.extract (7 * k) ws.size)

/-- A generator of words, the state of SplitMix64. -/
abbrev Gen := StateM UInt64

/-- The next word of SplitMix64. -/
def next : Gen UInt64 := modifyGet fun s =>
  let (s', v) := Library.Random.SplitMix64.splitMix s
  (v, s')

/-- A word below `n`, for a positive `n`. -/
def below (n : UInt64) : Gen UInt64 := return (← next) % n

/-- A record of a random stream with client tag `tag`, after `issued` orders, and whether it is an
order: a limit order at a price from `lo` to `lo + span - 1` of a quantity from 1 to `qmax` in any
time in force, a market order of up to twice `qmax`, or a cancel or a reduction of an id from 1 to
`issued + 1`, from accounts 1 to 3. -/
def record (lo span qmax issued tag : UInt64) : Gen (List UInt64 × Bool) := do
  let r ← below 100
  let side ← below 2
  let account := 1 + (← below 3)
  if r < 50 then
    return (Samples.limit side (lo + (← below span)) (1 + (← below qmax)) account tag
      (← below 3), true)
  else if r < 60 then
    return (Samples.market side (1 + (← below (2 * qmax))) account tag, true)
  else if r < 85 then
    return (Samples.cancel (1 + (← below (issued + 1))) account, false)
  else
    return (Samples.reduce (1 + (← below (issued + 1))) account (1 + (← below qmax)), false)

/-- `n` records of `record` from the seed `seed`. -/
def randomStream (seed : UInt64) (n : Nat) (lo span qmax : UInt64) : Array UInt64 :=
  let gen : Gen (Array UInt64) := do
    let mut ws : Array UInt64 := #[]
    let mut issued : UInt64 := 0
    for i in [0:n] do
      let (words, order) ← record lo span qmax issued (i + 1).toUInt64
      ws := ws ++ words.toArray
      if order then issued := issued + 1
    return ws
  (gen.run' seed).run

/-- Writes the cases' files and prints the cases. -/
def cases : IO Unit := do
  IO.FS.createDirAll dir
  let empty := Program.init ()
  let mut i := 1
  for s in Samples.samples do
    emit s!"sample-{i}" empty (s.setup ++ s.shown).toArray
    unless s.setup.isEmpty do
      emitRest s!"sample-{i}" empty (s.setup ++ s.shown).toArray (s.setup.length / 7)
    i := i + 1
  i := 1
  for ws in Samples.single do
    emit s!"single-{i}" empty ws
    i := i + 1
  for e in Edges.edges do
    let b := { empty with nextId := e.nextId }
    emit s!"edge-{e.name}" b e.words.toArray
    emitRest s!"edge-{e.name}" b e.words.toArray (e.words.length / 14)
  let randoms := [("random-narrow-1", randomStream 1 2000 500 11 20),
    ("random-narrow-2", randomStream 2 2000 500 11 20),
    ("random-wide-3", randomStream 3 3000 1 1023 4294967295)]
  for (name, ws) in randoms do
    emit name empty ws
    emitRest name empty ws (ws.size / 21)
    emitRest name empty ws (2 * (ws.size / 21))

end TestSupport.OrderBook.Cases
