import LeanExe.Ascii.Json

namespace LeanExe
namespace Examples.JsonDouble

def parseObject (text : AsciiString) : Option UInt64 :=
  match Ascii.expectWsByte text 0 Ascii.byteLBrace with
  | none => none
  | some pos1 =>
      match Ascii.Json.expectFieldName1 text pos1 Ascii.byteN with
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

def resultPrefix : ByteArray :=
  "{\"result\":".toUTF8

def resultJson (n : UInt64) : ByteArray :=
  (Ascii.appendUInt64Decimal resultPrefix n).push Ascii.byteRBrace

def doubleFits (n : UInt64) : Bool :=
  !(n > (9223372036854775807 : UInt64))

def transformAscii (text : AsciiString) : ByteArray :=
  match parseObject text with
  | some n =>
      if doubleFits n then
        resultJson (n * 2)
      else
        Ascii.Json.errorJson
  | none => Ascii.Json.errorJson

def transform (input : ByteArray) : ByteArray :=
  match AsciiString.ofByteArray? input with
  | some text => transformAscii text
  | none => Ascii.Json.errorJson

end Examples.JsonDouble
end LeanExe
