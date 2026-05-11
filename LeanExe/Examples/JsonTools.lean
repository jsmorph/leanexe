import LeanExe.Ascii.Json

namespace LeanExe.Examples.JsonTools

def lookupFieldOrZero (text : AsciiString) : UInt64 :=
  match Ascii.Json.getUInt64Field text "n".toUTF8 with
  | some n => n
  | none => 0

def parseSingleN (text : AsciiString) : Option UInt64 :=
  match Ascii.expectWsByte text 0 Ascii.byteLBrace with
  | some pos0 =>
      match Ascii.Json.expectFieldName text pos0 "n".toUTF8 with
      | some valuePos =>
          match Ascii.parseUInt64 text (Ascii.skipWs text valuePos) with
          | some parsed =>
              match Ascii.expectWsByte text parsed.pos Ascii.byteRBrace with
              | some endPos =>
                  if Ascii.skipWs text endPos == text.size then
                    some parsed.value
                  else
                    none
              | none => none
          | none => none
      | none => none
  | none => none

def transformAscii (text : AsciiString) : ByteArray :=
  match parseSingleN text with
  | some n =>
      let value := n + 1
      if value == 0 then
        Ascii.Json.errorJson
      else
        Ascii.Json.object1UInt64 "value".toUTF8 value
  | none => Ascii.Json.errorJson

def transform (input : ByteArray) : ByteArray :=
  match AsciiString.ofByteArray? input with
  | some text => transformAscii text
  | none => Ascii.Json.errorJson

def lookup (input : ByteArray) : UInt64 :=
  match AsciiString.ofByteArray? input with
  | some text => lookupFieldOrZero text
  | none => 0

end LeanExe.Examples.JsonTools
