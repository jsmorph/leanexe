import LeanExe.ByteIO

namespace LeanExe.Examples.RunningSum

structure Decimal where
  negative : Bool
  digits : ByteArray

def parse (line : ByteArray) : Option Decimal := Id.run do
  let stop := if line.size > 0 && line[line.size - 1]! == 13 then
    line.size - 1 else line.size
  let signed := stop > 0 && (line[0]! == 43 || line[0]! == 45)
  let start := if signed then 1 else 0
  if start == stop then return none
  let mut first := start
  for i in [start:stop] do
    let byte := line[i]!
    if byte < 48 || byte > 57 then return none
    if i == first && byte == 48 then first := first + 1
  return some ⟨line[0]! == 45 && first < stop, line.extract first stop⟩

def magnitudeLess (a b : ByteArray) : Bool := Id.run do
  if a.size != b.size then return a.size < b.size
  for i in [:a.size] do
    if a[i]! != b[i]! then return a[i]! < b[i]!
  return false

def combineMagnitude (a b : ByteArray) (subtract : Bool) : ByteArray := Id.run do
  let mut reversed := ByteArray.empty
  let mut carry : UInt64 := 0
  for i in [:max a.size b.size] do
    let x := if i < a.size then a[a.size - 1 - i]!.toUInt64 - 48 else 0
    let y := if i < b.size then b[b.size - 1 - i]!.toUInt64 - 48 else 0
    let digit := if subtract then 10 + x - y - carry else x + y + carry
    reversed := reversed.push (digit % 10).toUInt8
    carry := if subtract then (if digit < 10 then 1 else 0) else digit / 10
  if !subtract && carry != 0 then reversed := reversed.push carry.toUInt8
  let mut size := reversed.size
  while size > 0 && reversed[size - 1]! == 0 do
    size := size - 1
  let mut digits := ByteArray.empty
  for i in [:size] do
    digits := digits.push (reversed[size - 1 - i]! + 48)
  return digits

def add (a b : Decimal) : Decimal :=
  if a.negative == b.negative then
    ⟨a.negative, combineMagnitude a.digits b.digits false⟩
  else if magnitudeLess a.digits b.digits then
    ⟨b.negative, combineMagnitude b.digits a.digits true⟩
  else
    ⟨a.negative, combineMagnitude a.digits b.digits true⟩

def render (value : Decimal) : ByteArray :=
  if value.digits.size == 0 then "0\n".toUTF8
  else if value.negative then ("-".toUTF8 ++ value.digits).push 10
  else value.digits.push 10

def emitSum (total : Decimal) (line : ByteArray) :
    LeanExe.ByteIO (Except UInt32 Decimal) := do
  match parse line with
  | none => pure (.error 28)
  | some value =>
      let next := add total value
      let status ← LeanExe.ByteIO.write (render next) 18446744073709551615
      if status != 0 then return .error status
      pure (.ok next)

def main : LeanExe.ByteIO UInt32 := do
  let mut total : Decimal := ⟨false, ByteArray.empty⟩
  let mut line := ByteArray.empty
  repeat
    match ← LeanExe.ByteIO.read 4096 18446744073709551615 with
    | .error code => return code
    | .ok bytes =>
        if bytes.size == 0 then
          if line.size == 0 then return 0
          match ← emitSum total line with
          | .error code => return code
          | .ok _ => return 0
        for i in [:bytes.size] do
          let byte := bytes[i]!
          if byte == 10 then
            match ← emitSum total line with
            | .error code => return code
            | .ok next =>
                total := next
                line := ByteArray.empty
          else
            line := line.push byte
  pure 0

end LeanExe.Examples.RunningSum
