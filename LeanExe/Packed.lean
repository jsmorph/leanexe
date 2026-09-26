namespace LeanExe.Packed

def getUInt32LE! (bytes : ByteArray) (offset : Nat) : UInt32 :=
  if offset + 4 ≤ bytes.size then
    bytes[offset]!.toUInt32 |||
      (bytes[offset + 1]!.toUInt32 <<< 8) |||
      (bytes[offset + 2]!.toUInt32 <<< 16) |||
      (bytes[offset + 3]!.toUInt32 <<< 24)
  else
    panic! "packed UInt32 read is outside the byte array"

def generateUInt32LE (size : Nat) (value : Nat → UInt32) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity (size * 4)
  for index in [:size] do
    let word := value index
    bytes := bytes.push word.toUInt8
    bytes := bytes.push (word >>> 8).toUInt8
    bytes := bytes.push (word >>> 16).toUInt8
    bytes := bytes.push (word >>> 24).toUInt8
  return bytes

def generateUInt8 (size : Nat) (value : Nat → UInt8) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity size
  for index in [:size] do
    bytes := bytes.push (value index)
  return bytes

end LeanExe.Packed
