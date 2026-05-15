import LeanExe.Ascii.Json

namespace LeanExe
namespace Examples.JsonAdd

def leftFieldName : ByteArray :=
  "a".toUTF8

def rightFieldName : ByteArray :=
  "b".toUTF8

def sumFieldName : ByteArray :=
  "sum".toUTF8

def checkedAdd (a b : UInt64) : Option UInt64 :=
  let sum := a + b
  if sum < a then
    none
  else
    some sum

def parseInput (text : AsciiString) : Option UInt64 :=
  do
    let a <- Ascii.Json.getUInt64Field text leftFieldName
    let b <- Ascii.Json.getUInt64Field text rightFieldName
    checkedAdd a b

def resultJson (n : UInt64) : ByteArray :=
  Ascii.Json.object1UInt64 sumFieldName n

def transformAscii (text : AsciiString) : ByteArray :=
  match parseInput text with
  | some sum => resultJson sum
  | none => Ascii.Json.errorJson

def transform (input : ByteArray) : ByteArray :=
  match AsciiString.ofByteArray? input with
  | some text => transformAscii text
  | none => Ascii.Json.errorJson

end Examples.JsonAdd
end LeanExe
