import LeanExe.Ascii.Basic

namespace LeanExe
namespace Ascii

structure ParsedUInt64 where
  pos : Nat
  value : UInt64

def isDigit (byte : UInt8) : Bool :=
  let value := byte.toUInt64
  !(value < (48 : UInt64)) && value < (58 : UInt64)

def digitValue (byte : UInt8) : UInt64 :=
  byte.toUInt64 - (48 : UInt64)

def digitByte (digit : UInt64) : UInt8 :=
  digit.toUInt8 + byteDigitZero

def decimalWillOverflow (acc digit : UInt64) : Bool :=
  acc > (1844674407370955161 : UInt64) ||
    (acc == (1844674407370955161 : UInt64) && digit > (5 : UInt64))

def parseUInt64Fuel : Nat -> AsciiString -> Nat -> UInt64 -> UInt64 -> Option ParsedUInt64
  | 0, _text, _pos, _acc, _seen => none
  | fuel + 1, text, pos, acc, seen =>
      if isDigit (text.getD pos 0) &&
          !(decimalWillOverflow acc (digitValue (text.getD pos 0))) then
        parseUInt64Fuel fuel text (pos + 1)
          (acc * 10 + digitValue (text.getD pos 0)) 1
      else
        if seen == 1 && !(isDigit (text.getD pos 0)) then
          some { pos := pos, value := acc }
        else
          none

def parseUInt64 (text : AsciiString) (pos : Nat) : Option ParsedUInt64 :=
  parseUInt64Fuel (text.size + 1) text pos 0 0

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
    out.push byteDigitZero
  else
    let rev := revDigitsFuel 20 n ByteArray.empty
    appendReverseFuel (rev.size + 1) rev rev.size out

end Ascii
end LeanExe
