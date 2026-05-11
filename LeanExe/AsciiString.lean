namespace LeanExe

structure AsciiString where
  bytes : ByteArray

namespace AsciiString

def empty : AsciiString :=
  { bytes := ByteArray.empty }

def ofTrustedByteArray (bytes : ByteArray) : AsciiString :=
  { bytes := bytes }

def toByteArray (s : AsciiString) : ByteArray :=
  s.bytes

def size (s : AsciiString) : Nat :=
  s.bytes.size

def isEmpty (s : AsciiString) : Bool :=
  s.bytes.isEmpty

def get! (s : AsciiString) (index : Nat) : UInt8 :=
  s.bytes[index]!

def get? (s : AsciiString) (index : Nat) : Option UInt8 :=
  s.bytes[index]?

def getD (s : AsciiString) (index : Nat) (fallback : UInt8) : UInt8 :=
  match s.get? index with
  | some byte => byte
  | none => fallback

def isAsciiByte (byte : UInt8) : Bool :=
  byte.toUInt64 < (128 : UInt64)

def pushTrustedByte (s : AsciiString) (byte : UInt8) : AsciiString :=
  { bytes := s.bytes.push byte }

def pushByte? (s : AsciiString) (byte : UInt8) : Option AsciiString :=
  if isAsciiByte byte then
    some (pushTrustedByte s byte)
  else
    none

def append (left right : AsciiString) : AsciiString :=
  { bytes := left.bytes.append right.bytes }

def extract (s : AsciiString) (start stop : Nat) : AsciiString :=
  { bytes := s.bytes.extract start stop }

def allAsciiFuel : Nat -> ByteArray -> Nat -> Bool
  | 0, _bytes, _index => false
  | fuel + 1, bytes, index =>
      if index == bytes.size || !(isAsciiByte bytes[index]!) then
        index == bytes.size
      else
        allAsciiFuel fuel bytes (index + 1)

def isAscii (bytes : ByteArray) : Bool :=
  allAsciiFuel (bytes.size + 1) bytes 0

def ofByteArray? (bytes : ByteArray) : Option AsciiString :=
  if isAscii bytes then
    some (ofTrustedByteArray bytes)
  else
    none

def singletonTrusted (byte : UInt8) : AsciiString :=
  pushTrustedByte empty byte

def singleton? (byte : UInt8) : Option AsciiString :=
  pushByte? empty byte

end AsciiString

end LeanExe
