namespace LeanExe.Examples.ByteArrayPrograms

def firstBytePlusArray (input : ByteArray) : Nat :=
  let a := Array.replicate 1 (5 : UInt64)
  if input.size == 0 then
    a[0]!.toNat
  else
    (ByteArray.get! input 0).toNat + a[0]!.toNat

def firstByteIsStar (input : ByteArray) : Bool :=
  if input.size == 0 then
    false
  else
    let b : UInt8 := ByteArray.get! input 0
    b == (42 : UInt8)

def nextByte (b : UInt8) : UInt8 :=
  UInt8.ofNat (b.toNat + 1)

def firstByteNextIsZero (input : ByteArray) : Bool :=
  if input.size == 0 then
    false
  else
    nextByte (ByteArray.get! input 0) == (0 : UInt8)

def firstByteLowNibble (input : ByteArray) : Nat :=
  if input.size == 0 then
    0
  else
    ((ByteArray.get! input 0) &&& (15 : UInt8)).toNat

def firstByteBangIndex (input : ByteArray) : Nat :=
  if input.isEmpty then
    0
  else
    input[0]!.toNat

def byteAtOrZero (input : ByteArray) (index : Nat) : Nat :=
  if index < input.size then
    input[index]!.toNat
  else
    0

def prefixPlusFirstByte (base : UInt64) (input : ByteArray) : UInt64 :=
  if input.isEmpty then
    base
  else
    base + UInt64.ofNat input[0]!.toNat

def emptyViaIsEmpty (input : ByteArray) : Bool :=
  input.isEmpty

end LeanExe.Examples.ByteArrayPrograms
