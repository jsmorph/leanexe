import LeanExe.Packed
import LeanExe.Float32
import LeanExe.Runtime

namespace LeanExe.Examples.Packed

def readWord (bytes : ByteArray) (offset : Nat) : UInt32 :=
  LeanExe.Packed.getUInt32LE! bytes offset

def makeWords (size : Nat) (offset : UInt32) : ByteArray :=
  LeanExe.Packed.generateUInt32LE size fun index => offset + index.toUInt32

def shifted (bytes : ByteArray) (shift : UInt32) : ByteArray :=
  LeanExe.Packed.generateUInt32LE (bytes.size / 4) fun index =>
    LeanExe.Float32.addBits (LeanExe.Packed.getUInt32LE! bytes (index * 4)) shift

def generateRead (size : Nat) (bytes : ByteArray) : ByteArray :=
  LeanExe.Packed.generateUInt32LE size fun index =>
    LeanExe.Packed.getUInt32LE! bytes (index * 4)

def generateStats (size : Nat) : UInt64 :=
  let bytes := makeWords size 17
  let count := LeanExe.Runtime.allocCount
  count + bytes.size.toUInt64 * 1000

def temporarySum (size : Nat) : UInt64 :=
  let bytes := makeWords size 17
  (LeanExe.Packed.getUInt32LE! bytes 0).toUInt64 +
    (LeanExe.Packed.getUInt32LE! bytes ((size - 1) * 4)).toUInt64

def generateSum (size : Nat) (offset : UInt32) : ByteArray :=
  LeanExe.Packed.generateUInt32LE size fun index => Id.run do
    let mut value := offset
    for n in [:index] do
      value := value + n.toUInt32
    return value

def repeatedAdd (size : Nat) (value : UInt32) : UInt32 := Id.run do
  let mut total : UInt32 := 0
  for _ in [:size] do
    total := total + value
  return total

def generatedWithCall (size : Nat) (bytes : ByteArray) : ByteArray :=
  LeanExe.Packed.generateUInt32LE size fun index =>
    repeatedAdd index (LeanExe.Packed.getUInt32LE! bytes 0)

def incremented (bytes : ByteArray) : ByteArray :=
  LeanExe.Packed.generateUInt32LE (bytes.size / 4) fun index =>
    LeanExe.Packed.getUInt32LE! bytes (index * 4) + 1

def repeatedOwned (count : Nat) : ByteArray := Id.run do
  let mut bytes := makeWords 4 17
  for _ in [:count] do
    bytes := incremented bytes
  return bytes

def repeatedOwnedSum (count : Nat) : UInt64 :=
  let bytes := repeatedOwned count
  (LeanExe.Packed.getUInt32LE! bytes 0).toUInt64

def repeatedBorrowed (initial : ByteArray) (count : Nat) : ByteArray := Id.run do
  let mut bytes := initial
  for _ in [:count] do
    bytes := incremented bytes
  return bytes

def repeatedBorrowedSum (initial : ByteArray) (count : Nat) : UInt64 :=
  let bytes := repeatedBorrowed initial count
  (LeanExe.Packed.getUInt32LE! bytes 0).toUInt64

end LeanExe.Examples.Packed
