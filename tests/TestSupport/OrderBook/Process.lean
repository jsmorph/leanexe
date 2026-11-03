import Demos.OrderBook.ProcessCodec
import TestSupport.OrderBook.Edges

/-! The scripted-host tests of [the order book's process](../../../Demos/OrderBook/Process.lean).
Each case runs `Process.runFrom` with a host that returns reads of a fixed number of bytes,
commits writes of at most a fixed number of bytes, makes every third write commit nothing when
`zeroWrites` is set, and returns errno 29 at a chosen read or write.  The expected output and status
are `expectedOutput` and `expectedStatus` of
[the codec](../../../Demos/OrderBook/ProcessCodec.lean), computed with `Spec.run`, and the cases
cover the samples, the single records, the edge streams, the ends of input with and without whole
words, a command whose events take 229,488 bytes, and errnos of reads and writes.  The program
prints one summary line and exits with status 1 on the first failure. -/

namespace TestSupport.OrderBook.Process

open LeanExe LeanExe.Wasi Demos.OrderBook

def wordBytes (ws : List UInt64) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for w in ws do
    for j in [0:8] do
      bytes := bytes.push (w >>> (8 * j).toUInt64).toUInt8
  return bytes

def byteList (bytes : ByteArray) : List UInt64 := bytes.data.toList.map UInt8.toUInt64

def expectedBytes (input : ByteArray) : ByteArray :=
  ⟨((Process.expectedOutput (byteList input)).map UInt64.toUInt8).toArray⟩

/-- The behavior of the scripted host: the bytes of each read, the most bytes that a write
commits, whether every third write commits nothing, and the read or write that returns errno
29. -/
structure Script where
  chunk : Nat
  writeSize : Nat := 1 <<< 30
  zeroWrites : Bool := false
  readErrorAt : Option Nat := none
  writeErrorAt : Option Nat := none

structure Result where
  outcome : Outcome UInt64
  output : ByteArray
  writes : Nat

def run (input : ByteArray) (script : Script) : IO Result := do
  let offset ← IO.mkRef 0
  let output ← IO.mkRef ByteArray.empty
  let reads ← IO.mkRef 0
  let writes ← IO.mkRef 0
  let host : NativeHost := {
    read := fun capacity => do
      let index ← reads.get
      reads.set (index + 1)
      if script.readErrorAt == some index then return .returned 29 Bytes.empty
      let start ← offset.get
      let count := min script.chunk (min capacity.toNat (input.size - start))
      offset.set (start + count)
      return .returned 0 ⟨input.extract start (start + count)⟩
    write := fun stream bytes => do
      if stream != .stdout then throw (IO.userError "the process wrote to stderr")
      let index ← writes.get
      writes.set (index + 1)
      let count := if script.zeroWrites && index % 3 == 2 then 0
        else min script.writeSize bytes.data.size
      output.modify (· ++ bytes.data.extract 0 count)
      return .returned (if script.writeErrorAt == some index then 29 else 0) count.toUInt64
    exit := fun _ => pure (.ok ()) }
  let outcome ← Demos.OrderBook.Process.process.runFrom host Demos.OrderBook.Process.initial
  return ⟨outcome, ← output.get, ← writes.get⟩

def fail (name : String) (script : Script) (what : String) : IO α :=
  throw (IO.userError s!"{name}, reads of {script.chunk} bytes, writes of at most \
    {script.writeSize} bytes{if script.zeroWrites then " with zero-byte writes" else ""}: {what}")

/-- A run of `input` returns `status` after writing `expected`. -/
def expect (name : String) (input expected : ByteArray) (status : UInt64) (script : Script) :
    IO Unit := do
  let result ← run input script
  match result.outcome with
  | .returned actual =>
      unless actual == status do fail name script s!"status {actual}, expected {status}"
  | .exited code => fail name script s!"exit {code}"
  | .trapped message => fail name script s!"trap {message}"
  unless result.output.data == expected.data do
    fail name script
      s!"{result.output.size} bytes written, expected {expected.size}, or they differ"

/-- A run of `input` returns `expectedStatus` after writing the bytes of `expectedOutput`. -/
def check (name : String) (input : ByteArray) (script : Script) : IO Unit :=
  expect name input (expectedBytes input) (Process.expectedStatus (byteList input)) script

/-- `leWords` takes time quadratic in the length of its input, so each stream computes its
expected output once for all its runs. -/
def checkEach (name : String) (input : ByteArray) (scripts : List Script) : IO Nat := do
  let expected := expectedBytes input
  let status := Process.expectedStatus (byteList input)
  for script in scripts do
    expect name input expected status script
  return scripts.length

/-- Every read size from 1 to 57 bytes and 4,096, each with whole writes and with short writes
that include zero-byte writes, or for a stream of more than 1,000 records a subset of the read
sizes and short writes of 997 bytes. -/
def checkAll (name : String) (input : ByteArray) : IO Nat := do
  let large := input.size > 56 * 1000
  let chunks := if large then [1, 2, 7, 8, 55, 56, 57, 4096]
    else (List.range 57).map (· + 1) ++ [4096]
  checkEach name input (chunks.flatMap fun chunk =>
    [{ chunk := chunk },
      { chunk := chunk, writeSize := if large then 997 else chunk % 13 + 1, zeroWrites := true }])

def streams : List (String × List UInt64) :=
  (Samples.samples.map fun s => (s!"sample {s.name}", s.setup ++ s.shown)) ++
    (Samples.single.zipIdx.map fun (r, i) => (s!"single record {i + 1}", r.toList)) ++
    (TestSupport.OrderBook.Edges.edges.map fun e => (s!"edge stream {e.name}", e.words))

def main : IO UInt32 := do
  try
    let mut runs := 0
    for (name, words) in streams do
      runs := runs + (← checkAll name (wordBytes words))
    -- Ends of input: no bytes, whole words of a final short record, and bytes that fill no word,
    -- with and without whole records and whole words before them.
    let first := Samples.samples.headD ⟨"", [], []⟩
    let base := first.setup ++ first.shown
    let extra : List UInt64 := [1, 0, 10, 5, 101, 1001]
    let tail := ByteArray.mk #[7, 1, 2, 3, 4, 5, 6]
    runs := runs + (← checkAll "empty input" ByteArray.empty)
    for k in [1:7] do
      runs := runs + (← checkAll s!"{k} words alone" (wordBytes (extra.take k)))
      runs := runs + (← checkAll s!"records and {k} words" (wordBytes (base ++ extra.take k)))
    for t in [1:8] do
      let bytes := tail.extract 0 t
      runs := runs + (← checkAll s!"{t} bytes alone" bytes)
      runs := runs + (← checkAll s!"records and {t} bytes" (wordBytes base ++ bytes))
      for k in [1:7] do
        runs := runs + (← checkAll s!"records, {k} words, and {t} bytes"
          (wordBytes (base ++ extra.take k) ++ bytes))
    -- Statuses of these cases, which `check` takes from `expectedStatus`, stated directly.
    expect "empty input, status" ByteArray.empty ByteArray.empty 0 { chunk := 4096 }
    expect "3 bytes alone, status" (tail.extract 0 3) ByteArray.empty 28 { chunk := 4096 }
    expect "records and 3 bytes, status" (wordBytes base ++ tail.extract 0 3)
      (expectedBytes (wordBytes base)) 28 { chunk := 5 }
    expect "records and 2 words, status" (wordBytes (base ++ extra.take 2))
      (expectedBytes (wordBytes (base ++ extra.take 2))) 0 { chunk := 5 }
    runs := runs + 4
    -- A market sell that trades with 4,096 bids: 4,098 events, 229,488 bytes in one batch.
    let sweep := wordBytes TestSupport.OrderBook.Edges.fuelSell
    let sweepOutput := expectedBytes sweep
    let sweepRecords := wordBytes (TestSupport.OrderBook.Edges.fuelSell.take (7 * 4096))
    let sweepEvents := sweepOutput.size - (expectedBytes sweepRecords).size
    unless sweepEvents == 229488 do
      throw (IO.userError s!"the sweep's events take {sweepEvents} bytes, expected 229,488")
    for writeSize in [1000, 4093, 65536] do
      for chunk in [57, 4096] do
        expect "sweep of 4,096 bids" sweep sweepOutput 0
          { chunk := chunk, writeSize := writeSize, zeroWrites := true }
        runs := runs + 1
    -- Errnos: a failed read stops the process after the events of the whole records before it,
    -- and a failed write stops it with the bytes that the writes committed.
    let errorInput := wordBytes base
    for chunk in [7, 56, 4096] do
      let eofRead := (errorInput.size + chunk - 1) / chunk
      for index in [0, 1, 2, 5] do
        let script : Script := { chunk := chunk, readErrorAt := some index }
        if index ≤ eofRead then
          let read := min (chunk * index) errorInput.size
          expect s!"read errno at read {index}" errorInput
            (expectedBytes (errorInput.extract 0 (56 * (read / 56)))) 29 script
        else
          check s!"read errno at read {index}, after EOF" errorInput script
        runs := runs + 1
    for index in [0, 1, 3] do
      let script : Script := { chunk := 56, writeSize := 5, writeErrorAt := some index }
      let result ← run errorInput script
      match result.outcome with
      | .returned 29 => pure ()
      | _ => fail s!"write errno at write {index}" script "status other than 29"
      let full := expectedBytes errorInput
      unless result.writes == index + 1 &&
          result.output.data == (full.extract 0 result.output.size).data &&
          result.output.size == 5 * (index + 1) do
        fail s!"write errno at write {index}" script "output other than the committed prefix"
      runs := runs + 1
    IO.println s!"orderbook process: {runs} scripted runs passed"
    return 0
  catch e =>
    IO.eprintln s!"orderbook-process: {e}"
    return 1

end TestSupport.OrderBook.Process

def main : IO UInt32 := TestSupport.OrderBook.Process.main
