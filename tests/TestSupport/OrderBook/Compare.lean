import Demos.OrderBook.Abstract
import TestSupport.OrderBook.Edges
import TestSupport.OrderBook.Words

/-! The native comparison of [the program](../../../Demos/OrderBook/Program.lean) with [the
specification](../../../Demos/OrderBook/Spec.lean) on command streams.

`stream FILE [NEXTID]` reads a stream of little-endian words and runs it from the empty book whose
next id is `NEXTID`, 1 by default, through `Spec.run` and through `Program.run` from
`Program.init`.  It runs the stream in parts of 1,000 records through both, each part from the
books that the previous part left, and checks after each part that the event words equal
`Spec.encodeAll` of the specification's events, that `toSpec` of the program's book equals the
specification's book, that `top` equals `Spec.top`, and that the program's book is well formed.
It then runs the whole stream through `Program.run` in one call and checks its events, book, and
top against the parts' results, which `Spec.run_append` equates with one run of `Spec.run`, and for
streams of at most 3,000 records it also checks one call of `Spec.run` on the whole stream.  It
prints the events, the next id, the resting orders, and the top of the book in the format of the
Python reference, and on a disagreement it writes the check to standard error and exits with
status 1.

`write DIR` writes the samples, the single records, and the edge streams to `DIR`, one file each,
and lists each file with its starting next id in `DIR/manifest.txt`.

`host FILE NEXTID DIR` runs the stream from `Program.init` with next id `NEXTID` and writes, in the
Wasmtime host's output format, the results of the export `run` to `DIR/run.txt` and of `top` on
the resulting book to `DIR/top.txt`, and the resulting book's arrays to `DIR/oid.bin` and the like,
for the module's tests. -/

namespace TestSupport.OrderBook.Compare

open Demos.OrderBook
open Demos.OrderBook.Abstract (toSpec)
open TestSupport.OrderBook.Words

/-- Records in each part of a stream. -/
def partRecords : Nat := 1000

/-- Largest number of records for which one call of `Spec.run` runs on the whole stream. -/
def oneCallRecords : Nat := 3000

def runFrom (b : Program.Book) (ws : Array UInt64) : Program.Book × Array UInt64 :=
  Program.run b.oid b.acct b.qty b.lvl b.nxt b.head b.tail b.nextId b.count ws

def topNat (b : Program.Book) : Nat × Nat × Nat × Nat :=
  let (bp, bq, ap, aq) := Program.top b
  (bp.toNat, bq.toNat, ap.toNat, aq.toNat)

/-- The slots of the chain from slot `s`, read for at most `fuel` slots, or `none` when the chain
does not end within `fuel` slots. -/
def chainSlots (b : Program.Book) : Nat → UInt64 → Option (List UInt64)
  | 0, _ => none
  | fuel + 1, s =>
    if s = 0 then some [] else (chainSlots b fuel b.nxt[s.toNat]!).map (s :: ·)

/-- Whether the program's book has the shape that the abstraction assumes: arrays of 4,097 and
2,048 words, a chain at each level of the band that ends within 4,097 slots and whose slots lie
from 1 to 4,096, hold an order, record the chain's level, and end at the level's tail, empty
levels outside the band, distinct slots across the chains, a slot in some chain for each slot that
holds an order, and a count equal to the number of these slots. -/
def wellFormed (b : Program.Book) : Except String Unit := do
  let sizes := [b.oid, b.acct, b.qty, b.lvl, b.nxt].all (·.size == 4097) &&
    [b.head, b.tail].all (·.size == 2048)
  unless sizes do throw "array sizes"
  let mut seen : Array Bool := Array.replicate 4097 false
  let mut total := 0
  for l in [0:2048] do
    let inBand : Bool := (1 ≤ l && l ≤ 1023) || (1025 ≤ l && l ≤ 2047)
    let h := b.head[l]!
    let t := b.tail[l]!
    if !inBand then
      unless h == 0 && t == 0 do throw s!"level {l} outside the band is not empty"
    else
      let some ss := chainSlots b 4097 h | throw s!"level {l}: chain does not end"
      unless (ss.getLast?.getD 0) == t do throw s!"level {l}: tail"
      for s in ss do
        unless 1 ≤ s && s ≤ 4096 do throw s!"level {l}: slot {s} out of range"
        unless b.oid[s.toNat]! != 0 do throw s!"level {l}: slot {s} free"
        unless b.lvl[s.toNat]! == l.toUInt64 do throw s!"level {l}: slot {s} level"
        if seen[s.toNat]! then throw s!"level {l}: slot {s} in two chains"
        seen := seen.set! s.toNat true
        total := total + 1
  for s in [1:4097] do
    if b.oid[s]! != 0 && !seen[s]! then throw s!"slot {s} holds an order outside the chains"
  unless b.count.toNat == total do throw s!"count {b.count} for {total} orders"

def require (what : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError what)

def requireWellFormed (what : String) (b : Program.Book) : IO Unit :=
  match wellFormed b with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"{what}: {e}")

/-- The comparison of `stream`: the program's book and event words after the whole stream, after
every check has passed. -/
def compare (ws : Array UInt64) (nextId : UInt64) : IO (Program.Book × Array UInt64) := do
  let specStart : Spec.Book := { Spec.empty with nextId }
  let progStart : Program.Book := { Program.init () with nextId }
  let partWords := 7 * partRecords
  let mut sb := specStart
  let mut pb := progStart
  let mut specOut : Array UInt64 := #[]
  let mut o := 0
  let mut k := 0
  while o < ws.size do
    let part := ws.extract o (o + partWords)
    let (sb', es) := Spec.run sb part.toList
    let (pb', out) := runFrom pb part
    let words := Spec.encodeAll es
    require s!"part {k}: events" (out == words)
    require s!"part {k}: book" (toSpec pb' == sb')
    require s!"part {k}: top" (topNat pb' == Spec.top sb')
    requireWellFormed s!"part {k}" pb'
    specOut := specOut ++ words
    sb := sb'
    pb := pb'
    o := o + partWords
    k := k + 1
  let (whole, out) := runFrom progStart ws
  require "whole stream: events" (out == specOut)
  require "whole stream: book" (toSpec whole == sb)
  require "whole stream: top" (topNat whole == Spec.top sb)
  requireWellFormed "whole stream" whole
  if ws.size ≤ 7 * oneCallRecords then
    let (sb1, es1) := Spec.run specStart ws.toList
    require "one call of Spec.run: book" (sb1 == sb)
    require "one call of Spec.run: events" (Spec.encodeAll es1 == specOut)
  return (whole, out)

/-- The output of the Python reference for the program's results. -/
def printReference (b : Program.Book) (out : Array UInt64) : IO Unit := do
  let stdout ← IO.getStdout
  let mut text := ""
  for e in [0:out.size / 7] do
    text := text ++ "event"
    for j in [0:7] do
      text := text ++ s!" {out[7 * e + j]!}"
    text := text ++ "\n"
    if text.utf8ByteSize > 65536 then
      stdout.putStr text
      text := ""
  let sb := toSpec b
  text := text ++ s!"next {sb.nextId}\n"
  for o in sb.bids do
    text := text ++ s!"bid {o.id} {o.account} {o.price} {o.qty}\n"
  for o in sb.asks do
    text := text ++ s!"ask {o.id} {o.account} {o.price} {o.qty}\n"
  let (bp, bq, ap, aq) := Program.top b
  text := text ++ s!"top {bp} {bq} {ap} {aq}\n"
  stdout.putStr text

def parseWord (s : String) : IO UInt64 :=
  match s.toNat? with
  | some n => if n < 2 ^ 64 then pure n.toUInt64 else throw (IO.userError s!"word {s} too large")
  | none => throw (IO.userError s!"not a word: {s}")

def writeAll (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  let mut manifest := ""
  let mut i := 1
  for s in Samples.samples do
    let name := s!"sample-{if i < 10 then "0" else ""}{i}.bin"
    IO.FS.writeBinFile (dir / name) (wordBytes (s.setup ++ s.shown).toArray)
    manifest := manifest ++ s!"{name} 1\n"
    i := i + 1
  i := 1
  for r in Samples.single do
    let name := s!"single-{i}.bin"
    IO.FS.writeBinFile (dir / name) (wordBytes r)
    manifest := manifest ++ s!"{name} 1\n"
    i := i + 1
  for e in Edges.edges do
    let name := s!"edge-{e.name}.bin"
    IO.FS.writeBinFile (dir / name) (wordBytes e.words.toArray)
    manifest := manifest ++ s!"{name} {e.nextId}\n"
  IO.FS.writeFile (dir / "manifest.txt") manifest

def writeHost (ws : Array UInt64) (nextId : UInt64) (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  let (b, out) := runFrom { Program.init () with nextId } ws
  let arrays := [("oid", b.oid), ("acct", b.acct), ("qty", b.qty), ("lvl", b.lvl),
    ("nxt", b.nxt), ("head", b.head), ("tail", b.tail)]
  let mut text := ""
  for (name, xs) in arrays do
    IO.FS.writeBinFile (dir / s!"{name}.bin") (wordBytes xs)
    text := text ++ hostArray xs ++ "\n"
  text := text ++ s!"{b.nextId}\n{b.count}\n" ++ hostArray out ++ "\n"
  IO.FS.writeFile (dir / "run.txt") text
  let (bp, bq, ap, aq) := Program.top b
  IO.FS.writeFile (dir / "top.txt") s!"{bp}\n{bq}\n{ap}\n{aq}\n"
  IO.FS.writeFile (dir / "book.txt") s!"{b.nextId} {b.count}\n"

end TestSupport.OrderBook.Compare

open TestSupport.OrderBook.Compare TestSupport.OrderBook.Words in
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["stream", file] | ["stream", file, _] =>
      let nextId ← match args with
        | [_, _, n] => parseWord n
        | _ => pure 1
      let (b, out) ← compare (← readWords file) nextId
      printReference b out
    | ["write", dir] => writeAll dir
    | ["host", file, n, dir] => writeHost (← readWords file) (← parseWord n) dir
    | _ =>
      IO.eprintln "usage: orderbook-compare stream FILE [NEXTID] | write DIR | host FILE NEXTID DIR"
      return 2
    return 0
  catch e =>
    IO.eprintln s!"orderbook-compare: {e}"
    return 1
