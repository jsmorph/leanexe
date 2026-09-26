import LeanExe.Packed

namespace LeanExe.Examples.Exports

def appendByte (input : ByteArray) (value : UInt8) : ByteArray := input.push value

def appendTwice (input : ByteArray) (value : UInt8) : ByteArray :=
  appendByte (appendByte input value) (value + 1)

def borrow (input : ByteArray) : ByteArray := input

def increment (value : UInt32) : UInt32 := value + 1

def wordIncrement (value : UInt64) : UInt64 := value + 1

def wordDouble (value : UInt64) : UInt64 := value * 2

end LeanExe.Examples.Exports
