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

def fnv1aStep (hash : UInt32) (byte : UInt8) : UInt32 :=
  (hash ^^^ byte.toUInt32) * (16777619 : UInt32)

def fnv1aFuel : Nat → ByteArray → Nat → UInt32 → UInt32
  | 0, _input, _index, hash => hash
  | fuel + 1, input, index, hash =>
      if index == input.size then
        hash
      else
        fnv1aFuel fuel input (index + 1) (fnv1aStep hash input[index]!)

def fnv1a32 (input : ByteArray) : UInt64 :=
  (fnv1aFuel (input.size + 1) input 0 (2166136261 : UInt32)).toUInt64

def emptyViaIsEmpty (input : ByteArray) : Bool :=
  input.isEmpty

end LeanExe.Examples.ByteArrayPrograms
