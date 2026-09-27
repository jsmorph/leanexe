import Init.Data.List.Lemmas

namespace Wasm.Encoding.Spec

abbrev Bytes := List UInt8

inductive Unsigned : Nat → Bytes → Nat → Prop
  | terminal (width : Nat) (byte : UInt8)
      (positive : 0 < width) (low : byte.toNat < 128)
      (fits : byte.toNat < 2 ^ width) :
      Unsigned width [byte] byte.toNat
  | next (width : Nat) (byte : UInt8) (tail : Bytes) (value : Nat)
      (positive : 0 < width) (high : 128 ≤ byte.toNat)
      (rest : Unsigned width tail value) :
      Unsigned (width + 7) (byte :: tail) (byte.toNat - 128 + 128 * value)

def signedDigit (byte : UInt8) : Int :=
  if byte.toNat < 64 then byte.toNat else (byte.toNat : Int) - 128

inductive Signed : Nat → Bytes → Int → Prop
  | terminal (width : Nat) (byte : UInt8)
      (positive : 0 < width) (low : byte.toNat < 128)
      (lower : -(2 ^ (width - 1) : Int) ≤ signedDigit byte)
      (upper : signedDigit byte < (2 ^ (width - 1) : Int)) :
      Signed width [byte] (signedDigit byte)
  | next (width : Nat) (byte : UInt8) (tail : Bytes) (value : Int)
      (positive : 0 < width) (high : 128 ≤ byte.toNat)
      (rest : Signed width tail value) :
      Signed (width + 7) (byte :: tail) ((byte.toNat : Int) - 128 + 128 * value)

inductive Items (relation : Bytes → α → Prop) : Bytes → List α → Prop
  | nil : Items relation [] []
  | cons (headBytes tailBytes : Bytes) (head : α) (tail : List α)
      (headEncoding : relation headBytes head)
      (tailEncoding : Items relation tailBytes tail) :
      Items relation (headBytes ++ tailBytes) (head :: tail)

inductive Vector (relation : Bytes → α → Prop) : Bytes → List α → Prop
  | intro (countBytes body : Bytes) (values : List α)
      (count : Unsigned 32 countBytes values.length)
      (items : Items relation body values) :
      Vector relation (countBytes ++ body) values

inductive Sized (relation : Bytes → α → Prop) : Bytes → α → Prop
  | intro (countBytes body : Bytes) (value : α)
      (count : Unsigned 32 countBytes body.length)
      (payload : relation body value) :
      Sized relation (countBytes ++ body) value

inductive Name : Bytes → String → Prop
  | intro (countBytes : Bytes) (value : String)
      (count : Unsigned 32 countBytes value.toUTF8.size) :
      Name (countBytes ++ value.toUTF8.data.toList) value

end Wasm.Encoding.Spec
