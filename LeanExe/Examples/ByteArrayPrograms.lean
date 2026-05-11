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

def byteAtQuestionOrZero (input : ByteArray) (index : Nat) : Nat :=
  match input[index]? with
  | some byte => byte.toNat
  | none => 0

def byteAtProofOrZero (input : ByteArray) : Nat :=
  if _h : 0 < input.size then
    input[0].toNat
  else
    0

def sliceSecondPlusSize (input : ByteArray) : Nat :=
  let slice := input.extract 1 3
  if slice.isEmpty then
    0
  else
    slice.size + slice[0]!.toNat

def sliceClampSize (input : ByteArray) : Nat :=
  (input.extract 1 10).size

def sliceStopBeforeStart (input : ByteArray) : Nat :=
  (input.extract 3 1).size

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

def foldSum (input : ByteArray) : Nat :=
  input.foldl (fun acc byte => acc + byte.toNat) 0

def foldWindowDecimal (input : ByteArray) : Nat :=
  input.foldl (fun acc byte => acc * 10 + byte.toNat) 0 1 3

def emptyViaIsEmpty (input : ByteArray) : Bool :=
  input.isEmpty

def bytesABC : ByteArray :=
  ((ByteArray.empty.push (65 : UInt8)).push (66 : UInt8)).push (67 : UInt8)

def mkABC : ByteArray :=
  ByteArray.mk #[(65 : UInt8), (66 : UInt8), (67 : UInt8)]

def appendBang (input : ByteArray) : ByteArray :=
  input.push (33 : UInt8)

def appendABCXYZ : ByteArray :=
  bytesABC.append
    (((ByteArray.empty.push (88 : UInt8)).push (89 : UInt8)).push (90 : UInt8))

def appendInputABC (input : ByteArray) : ByteArray :=
  input.append bytesABC

def appendNotationABCXYZ : ByteArray :=
  bytesABC ++ ByteArray.mk #[(88 : UInt8), (89 : UInt8), (90 : UInt8)]

def setABC : ByteArray :=
  if h : 1 < bytesABC.size then
    bytesABC.set 1 (90 : UInt8) h
  else
    bytesABC

def setFirstBang (input : ByteArray) : ByteArray :=
  if h : 0 < input.size then
    input.set 0 (33 : UInt8) h
  else
    input

def setBangABC : ByteArray :=
  bytesABC.set! 2 (90 : UInt8)

def setBangFirstQuestion (input : ByteArray) : ByteArray :=
  if input.isEmpty then
    input
  else
    input.set! 0 (63 : UInt8)

def copyInputMiddle (input : ByteArray) : ByteArray :=
  input.copySlice 1 bytesABC 1 2

def copyInputPastDest (input : ByteArray) : ByteArray :=
  input.copySlice 0 bytesABC 10 2 false

def copyShortSource : ByteArray :=
  (ByteArray.empty.push (88 : UInt8)).copySlice 0 bytesABC 1 3

def tailSlice (input : ByteArray) : ByteArray :=
  input.extract 1 input.size

end LeanExe.Examples.ByteArrayPrograms
