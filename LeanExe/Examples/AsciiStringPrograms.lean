import LeanExe.AsciiString

namespace LeanExe
namespace Examples.AsciiStringPrograms

def validAscii (input : ByteArray) : Bool :=
  AsciiString.isAscii input

def checkedSize (input : ByteArray) : Nat :=
  match AsciiString.ofByteArray? input with
  | some text => text.size
  | none => 0

def firstOrQuestion (input : ByteArray) : UInt64 :=
  match AsciiString.ofByteArray? input with
  | some text => text.getD 0 (63 : UInt8) |>.toUInt64
  | none => 63

def identityTrusted (text : AsciiString) : AsciiString :=
  text

def appendBangOrQuestion (input : ByteArray) : ByteArray :=
  match AsciiString.ofByteArray? input with
  | some text =>
      AsciiString.toByteArray
        (AsciiString.pushTrustedByte text (33 : UInt8))
  | none =>
      AsciiString.toByteArray (AsciiString.singletonTrusted (63 : UInt8))

def pushIfAscii (input : ByteArray) (byte : UInt64) : ByteArray :=
  match AsciiString.ofByteArray? input with
  | some text =>
      match text.pushByte? byte.toUInt8 with
      | some output => output.toByteArray
      | none => ByteArray.empty
  | none => ByteArray.empty

def appendSelfTrusted (input : ByteArray) : ByteArray :=
  let text := AsciiString.ofTrustedByteArray input
  AsciiString.toByteArray (AsciiString.append text text)

def prefixBangTrusted (input : ByteArray) : ByteArray :=
  let text := AsciiString.ofTrustedByteArray input
  AsciiString.toByteArray
    (AsciiString.append
      (AsciiString.singletonTrusted (33 : UInt8))
      text)

def middle (input : ByteArray) : ByteArray :=
  match AsciiString.ofByteArray? input with
  | some text => AsciiString.toByteArray (text.extract 1 3)
  | none => ByteArray.empty

def equalsABC (input : ByteArray) : Bool :=
  match AsciiString.ofByteArray? input with
  | some text => text.equals (AsciiString.ofTrustedByteArray "abc".toUTF8)
  | none => false

def startsWithAB (input : ByteArray) : Bool :=
  match AsciiString.ofByteArray? input with
  | some text => text.startsWith (AsciiString.ofTrustedByteArray "ab".toUTF8)
  | none => false

def containsColon (input : ByteArray) : Bool :=
  match AsciiString.ofByteArray? input with
  | some text => text.containsByte (58 : UInt8)
  | none => false

end Examples.AsciiStringPrograms
end LeanExe
