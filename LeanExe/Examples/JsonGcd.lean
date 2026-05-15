import LeanExe.Ascii.Json

namespace LeanExe
namespace Examples.JsonGcd

def resultFieldName : ByteArray :=
  "gcd".toUTF8

structure GcdState where
  seen : Bool
  failed : Bool
  value : UInt64

def gcdFuel : Nat -> UInt64 -> UInt64 -> Option UInt64
  | 0, _a, _b => none
  | fuel + 1, a, b =>
      if b == 0 then
        some a
      else
        gcdFuel fuel b (a % b)

def gcd? (a b : UInt64) : Option UInt64 :=
  gcdFuel 128 a b

def addRange (text : AsciiString) (state : GcdState) (range : Ascii.Json.FieldRange) :
    GcdState :=
  if state.failed then
    state
  else
    match Ascii.Json.parseUInt64Range text range with
    | none => { state with failed := true }
    | some value =>
        if state.seen then
          match gcd? state.value value with
          | some next => { state with value := next }
          | none => { state with failed := true }
        else
          { seen := true, failed := false, value := value }

def foldRangesFuel :
    Nat -> AsciiString -> Array Ascii.Json.FieldRange -> Nat -> GcdState -> GcdState
  | 0, _text, _ranges, _index, state => { state with failed := true }
  | fuel + 1, text, ranges, index, state =>
      if state.failed || index == ranges.size then
        state
      else
        foldRangesFuel fuel text ranges (index + 1) (addRange text state ranges[index]!)

def foldRanges (text : AsciiString) (ranges : Array Ascii.Json.FieldRange) : GcdState :=
  foldRangesFuel (ranges.size + 1) text ranges 0
    { seen := false, failed := false, value := 0 }

def gcdInput? (text : AsciiString) : Option UInt64 :=
  match Ascii.Json.parseArrayRanges text with
  | none => none
  | some ranges =>
      let state := foldRanges text ranges
      if state.failed || !state.seen then
        none
      else
        some state.value

def requireGcdInput (text : AsciiString) : Except ByteArray UInt64 :=
  match gcdInput? text with
  | some value => Except.ok value
  | none => Except.error Ascii.Json.errorJson

def transformAscii (text : AsciiString) : Except ByteArray ByteArray :=
  do
    let value <- requireGcdInput text
    pure (Ascii.Json.object1UInt64 resultFieldName value)

def transform (input : ByteArray) : Except ByteArray ByteArray :=
  match AsciiString.ofByteArray? input with
  | some text => transformAscii text
  | none => Except.error Ascii.Json.errorJson

end Examples.JsonGcd
end LeanExe
