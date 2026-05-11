import LeanExe.Ascii.Json
import LeanExe.Examples.Collatz

namespace LeanExe
namespace Examples.JsonCollatzLength

def fieldName : ByteArray :=
  ByteArray.mk #[
    (99 : UInt8), (111 : UInt8), (108 : UInt8), (108 : UInt8),
    (97 : UInt8), (116 : UInt8), (122 : UInt8), (76 : UInt8),
    (101 : UInt8), (110 : UInt8), (103 : UInt8), (116 : UInt8),
    (104 : UInt8), (70 : UInt8), (111 : UInt8), (114 : UInt8)
  ]

def parseObject (text : AsciiString) : Option UInt64 :=
  match Ascii.expectWsByte text 0 Ascii.byteLBrace with
  | none => none
  | some pos1 =>
      match Ascii.Json.expectFieldName text pos1 fieldName with
      | none => none
      | some valuePos =>
          match Ascii.parseUInt64 text (Ascii.skipWs text valuePos) with
          | none => none
          | some parsed =>
              match Ascii.expectWsByte text parsed.pos Ascii.byteRBrace with
              | none => none
              | some endPos =>
                  if Ascii.skipWs text endPos == text.size then
                    some parsed.value
                  else
                    none

def lengthPrefix : ByteArray :=
  ByteArray.mk #[
    Ascii.byteLBrace, Ascii.byteQuote, (108 : UInt8), (101 : UInt8),
    (110 : UInt8), (103 : UInt8), (116 : UInt8), (104 : UInt8),
    Ascii.byteQuote, Ascii.byteColon
  ]

def resultJson (n : UInt64) : ByteArray :=
  (Ascii.appendUInt64Decimal lengthPrefix n).push Ascii.byteRBrace

def transformAscii (text : AsciiString) : ByteArray :=
  match parseObject text with
  | some n =>
      match Collatz.length? n with
      | some len => resultJson len
      | none => Ascii.Json.errorJson
  | none => Ascii.Json.errorJson

def transform (input : ByteArray) : ByteArray :=
  match AsciiString.ofByteArray? input with
  | some text => transformAscii text
  | none => Ascii.Json.errorJson

end Examples.JsonCollatzLength
end LeanExe
