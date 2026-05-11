import LeanExe.AsciiString

namespace LeanExe
namespace Examples.JsonDouble

structure ParsedNumber where
  pos : Nat
  value : UInt64

def lbrace : UInt8 := 123
def rbrace : UInt8 := 125
def quote : UInt8 := 34
def colon : UInt8 := 58
def byteN : UInt8 := 110
def digitZero : UInt8 := 48

def isWs (byte : UInt8) : Bool :=
  byte == (32 : UInt8) ||
    byte == (9 : UInt8) ||
    byte == (10 : UInt8) ||
    byte == (13 : UInt8)

def isDigit (byte : UInt8) : Bool :=
  let value := byte.toUInt64
  !(value < (48 : UInt64)) && value < (58 : UInt64)

def digitValue (byte : UInt8) : UInt64 :=
  byte.toUInt64 - (48 : UInt64)

def digitByte (digit : UInt64) : UInt8 :=
  digit.toUInt8 + digitZero

def skipWsFuel : Nat -> AsciiString -> Nat -> Nat
  | 0, _text, pos => pos
  | fuel + 1, text, pos =>
      if isWs (text.getD pos 0) then
        skipWsFuel fuel text (pos + 1)
      else
        pos

def skipWs (text : AsciiString) (pos : Nat) : Nat :=
  skipWsFuel (text.size + 1) text pos

def expectByte (text : AsciiString) (pos : Nat) (byte : UInt8) : Option Nat :=
  if pos < text.size && text.get! pos == byte then
    some (pos + 1)
  else
    none

def expectWsByte (text : AsciiString) (pos : Nat) (byte : UInt8) : Option Nat :=
  expectByte text (skipWs text pos) byte

def decimalWillOverflow (acc digit : UInt64) : Bool :=
  acc > (1844674407370955161 : UInt64) ||
    (acc == (1844674407370955161 : UInt64) && digit > (5 : UInt64))

def parseUIntFuel : Nat -> AsciiString -> Nat -> UInt64 -> UInt64 -> Option ParsedNumber
  | 0, _text, _pos, _acc, _seen => none
  | fuel + 1, text, pos, acc, seen =>
      if isDigit (text.getD pos 0) &&
          !(decimalWillOverflow acc (digitValue (text.getD pos 0))) then
        parseUIntFuel fuel text (pos + 1)
          (acc * 10 + digitValue (text.getD pos 0)) 1
      else
        if seen == 1 && !(isDigit (text.getD pos 0)) then
          some { pos := pos, value := acc }
        else
          none

def parseUInt (text : AsciiString) (pos : Nat) : Option ParsedNumber :=
  parseUIntFuel (text.size + 1) text pos 0 0

def parseObject (text : AsciiString) : Option UInt64 :=
  match expectWsByte text 0 lbrace with
  | none => none
  | some pos1 =>
      match expectWsByte text pos1 quote with
      | none => none
      | some pos2 =>
          match expectByte text pos2 byteN with
          | none => none
          | some pos3 =>
              match expectByte text pos3 quote with
              | none => none
              | some pos4 =>
                  match expectWsByte text pos4 colon with
                  | none => none
                  | some pos5 =>
                      match parseUInt text (skipWs text pos5) with
                      | none => none
                      | some parsed =>
                          match expectWsByte text parsed.pos rbrace with
                          | none => none
                          | some endPos =>
                              if skipWs text endPos == text.size then
                                some parsed.value
                              else
                                none

def resultPrefix : ByteArray :=
  (((((((((ByteArray.empty.push lbrace).push quote).push (114 : UInt8)).push (101 : UInt8)).push
    (115 : UInt8)).push (117 : UInt8)).push (108 : UInt8)).push (116 : UInt8)).push quote).push
    colon

def errorJson : ByteArray :=
  ((((((((((ByteArray.empty.push lbrace).push quote).push (101 : UInt8)).push (114 : UInt8)).push
    (114 : UInt8)).push (111 : UInt8)).push (114 : UInt8)).push quote).push colon).push
    (49 : UInt8)).push rbrace

def revDigitsFuel : Nat -> UInt64 -> ByteArray -> ByteArray
  | 0, _n, out => out
  | fuel + 1, n, out =>
      if n == 0 then
        out
      else
        revDigitsFuel fuel (n / 10) (out.push (digitByte (n % 10)))

def appendReverseFuel : Nat -> ByteArray -> Nat -> ByteArray -> ByteArray
  | 0, _rev, _index, out => out
  | fuel + 1, rev, index, out =>
      if index == 0 then
        out
      else
        appendReverseFuel fuel rev (index - 1) (out.push rev[index - 1]!)

def appendUInt64Decimal (out : ByteArray) (n : UInt64) : ByteArray :=
  if n == 0 then
    out.push digitZero
  else
    let rev := revDigitsFuel 20 n ByteArray.empty
    appendReverseFuel (rev.size + 1) rev rev.size out

def resultJson (n : UInt64) : ByteArray :=
  (appendUInt64Decimal resultPrefix n).push rbrace

def doubleFits (n : UInt64) : Bool :=
  !(n > (9223372036854775807 : UInt64))

def transformAscii (text : AsciiString) : ByteArray :=
  match parseObject text with
  | some n =>
      if doubleFits n then
        resultJson (n * 2)
      else
        errorJson
  | none => errorJson

def transform (input : ByteArray) : ByteArray :=
  match AsciiString.ofByteArray? input with
  | some text => transformAscii text
  | none => errorJson

end Examples.JsonDouble
end LeanExe
