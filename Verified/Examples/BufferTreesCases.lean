import Verified.Examples.BufferTrees
import TestSupport.Host

/-! The cases of the trees whose records hold byte buffers.  Each case passes a buffer and returns
a word, and the code builds, copies, reads, and consumes the trees in between.  The block count of
each case is 0: the function takes its buffer argument as owned, and the code releases that buffer
and every record and buffer that it allocates before the function returns. -/

namespace Verified.Examples.BufferTrees

open TestSupport.Host

def hex (b : LeanExe.Bytes) : String :=
  String.join (b.data.toList.map fun byte =>
    let digits := Nat.toDigits 16 byte.toNat
    String.ofList (if digits.length < 2 then '0' :: digits else digits))

def cases : IO Unit := do
  let names : List LeanExe.Bytes := [.empty, bytes![0], bytes![7, 255], bytes![1, 2, 3, 4, 5],
    ⟨⟨(List.range 40).toArray.map UInt8.ofNat⟩⟩, ⟨⟨(List.range 300).toArray.map UInt8.ofNat⟩⟩]
  for n in names do
    IO.println s!"buffertrees|counted|i64|bytes:{hex n}|{counted n}|0"
    IO.println s!"buffertrees|firstByte|i64|bytes:{hex n}|{firstByte n}|0"
  for k in [0, 4, maxU] do
    IO.println s!"buffertrees|unnamed|i64|i64:{k}|{unnamed k}|0"

end Verified.Examples.BufferTrees
