import LeanExe.Ascii.Decimal

namespace LeanExe
namespace Ascii
namespace Json

def expectFieldName1 (text : AsciiString) (pos : Nat) (name : UInt8) : Option Nat :=
  match expectWsByte text pos byteQuote with
  | none => none
  | some pos1 =>
      match expectByte text pos1 name with
      | none => none
      | some pos2 =>
          match expectByte text pos2 byteQuote with
          | none => none
          | some pos3 => expectWsByte text pos3 byteColon

def expectBytesFuel : Nat -> AsciiString -> Nat -> ByteArray -> Nat -> Option Nat
  | 0, _text, _pos, _name, _index => none
  | fuel + 1, text, pos, name, index =>
      if !(index == name.size) && pos < text.size && text.get! pos == name.get! index then
        expectBytesFuel fuel text (pos + 1) name (index + 1)
      else
        if index == name.size then
          some pos
        else
          none

def expectBytes (text : AsciiString) (pos : Nat) (name : ByteArray) : Option Nat :=
  expectBytesFuel (name.size + 1) text pos name 0

def expectFieldName (text : AsciiString) (pos : Nat) (name : ByteArray) : Option Nat :=
  match expectWsByte text pos byteQuote with
  | none => none
  | some pos1 =>
      match expectBytes text pos1 name with
      | none => none
      | some pos2 =>
          match expectByte text pos2 byteQuote with
          | none => none
          | some pos3 => expectWsByte text pos3 byteColon

def errorJson : ByteArray :=
  "{\"error\":1}".toUTF8

end Json
end Ascii
end LeanExe
