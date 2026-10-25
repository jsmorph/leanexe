import LeanExe.Dialect.Build
import LeanExe.Dialect.Bytes
import LeanExe.Dialect.Loop
import LeanExe.Dialect.RepeatWhile

namespace Demos.RunningSum

structure Decimal where
  negative : Bool
  digits : Array UInt64
  deriving Inhabited, Repr

structure Parsed where
  valid : Bool
  value : Decimal
  deriving Inhabited, Repr

def zero : Decimal := ⟨false, #[]⟩

def parse (line : Array UInt64) : Parsed :=
  let length := line.size.toUInt64
  let firstByte : UInt64 := if length == 0 then 0 else line[(0 : UInt64).toNat]!
  let stop := if length > 0 && line[(length - 1).toNat]! == 13 then length - 1 else length
  let signed := stop > 0 && (firstByte == 43 || firstByte == 45)
  let start : UInt64 := if signed then 1 else 0
  let scanned := LeanExe.loop stop (start, true) fun i state =>
    if i < start then state
    else
      let byte := line[i.toNat]!
      let valid := state.2 && byte ≥ 48 && byte ≤ 57
      let first := if i == state.1 && byte == 48 then state.1 + 1 else state.1
      (first, valid)
  let digits := LeanExe.build (stop - scanned.1) fun i => line[(scanned.1 + i).toNat]!
  ⟨start < stop && scanned.2, ⟨firstByte == 45 && scanned.1 < stop, digits⟩⟩

def magnitudeLess (a b : Array UInt64) : Bool :=
  if a.size.toUInt64 != b.size.toUInt64 then a.size.toUInt64 < b.size.toUInt64
  else
    let order := LeanExe.loop a.size.toUInt64 (0 : UInt64) fun i order =>
      if order != 0 then order
      else if a[i.toNat]! < b[i.toNat]! then 1
      else if b[i.toNat]! < a[i.toNat]! then 2
      else 0
    order == 1

def combineMagnitude (a b : Array UInt64) (subtract : Bool) : Array UInt64 :=
  let aSize := a.size.toUInt64
  let bSize := b.size.toUInt64
  let count := max aSize bSize
  let result := LeanExe.loop count (#[], (0 : UInt64)) fun i state =>
    let x := if i < aSize then a[(aSize - 1 - i).toNat]! - 48 else 0
    let y := if i < bSize then b[(bSize - 1 - i).toNat]! - 48 else 0
    let digit := if subtract then 10 + x - y - state.2 else x + y + state.2
    let carry := if subtract then (if digit < 10 then 1 else 0) else digit / 10
    (state.1.push (digit % 10), carry)
  let reversed := if !subtract && result.2 != 0 then result.1.push result.2 else result.1
  let size := LeanExe.repeatWhile reversed.size.toUInt64 reversed.size.toUInt64
    (fun size => size > 0 && reversed[(size - 1).toNat]! == 0) (fun size => size - 1)
  LeanExe.build size fun i => reversed[(size - 1 - i).toNat]! + 48

def add (a b : Decimal) : Decimal :=
  if a.negative == b.negative then
    ⟨a.negative, combineMagnitude a.digits b.digits false⟩
  else if magnitudeLess a.digits b.digits then
    ⟨b.negative, combineMagnitude b.digits a.digits true⟩
  else
    ⟨a.negative, combineMagnitude a.digits b.digits true⟩

def render (value : Decimal) : LeanExe.Bytes :=
  if value.digits.size.toUInt64 == 0 then bytes![48, 10]
  else
    let signWidth : UInt64 := if value.negative then 1 else 0
    let length := value.digits.size.toUInt64 + signWidth
    LeanExe.Bytes.build (length + 1) fun i =>
      if i == length then 10
      else if signWidth == 1 && i == 0 then 45
      else value.digits[(i - signWidth).toNat]!

end Demos.RunningSum
