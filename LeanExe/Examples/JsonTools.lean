import LeanExe.Ascii.Json

namespace LeanExe.Examples.JsonTools

def lookupFieldOrZero (text : AsciiString) : UInt64 :=
  match Ascii.Json.getUInt64Field text "n".toUTF8 with
  | some n => n
  | none => 0

def parseSingleN (text : AsciiString) : Option UInt64 :=
  Ascii.Json.getUInt64Field text "n".toUTF8

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
