module

public import Verified.Reflect.Command

@[expose] public section

/-! Updates of a buffer with `LeanExe.Bytes.set`, which `tests/wasi/run.sh` and
`tests/native/bytes.sh` run with the cases of `tests/wasi/bytes-set.tsv`.  `setByte` takes its
buffer as owned, and the update writes into the buffer's block.  `setTwice` updates its buffer and
then the owned result of that update.  `fillFrom` updates each byte of its buffer in a loop whose
state is the buffer.  `setKept` reads its buffer after the update, so the update writes into a
copy, which the read of the copy releases.  `setEmpty` updates the empty buffer, which has no
byte to write. -/

namespace Verified.Examples.BytesSet

def setByte (bytes : LeanExe.Bytes) (index value : UInt64) : LeanExe.Bytes :=
  bytes.set index value

def setTwice (bytes : LeanExe.Bytes) (first second value : UInt64) : LeanExe.Bytes :=
  let once := bytes.set first value
  once.set second (value + 1)

def fillFrom (bytes : LeanExe.Bytes) (start : UInt64) : LeanExe.Bytes :=
  LeanExe.loop bytes.size bytes fun i b => b.set i (start + i)

def setKept (bytes : LeanExe.Bytes) (index value : UInt64) : UInt64 :=
  (bytes.set index value).get index + 256 * bytes.get index

def setEmpty (index value : UInt64) : LeanExe.Bytes :=
  LeanExe.Bytes.empty.set index value

verified_compile compiled := [setByte, setTwice, fillFrom, setKept, setEmpty]

end Verified.Examples.BytesSet
