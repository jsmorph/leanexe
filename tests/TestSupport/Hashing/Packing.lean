/-! Conversions between hexadecimal text, bytes, packed words, and bit messages for the hashing
tests. -/

namespace TestSupport.Hashing.Packing

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

def bytesOfHex (s : String) : List UInt8 :=
  let cs := s.toList.toArray
  (List.range (cs.size / 2)).map fun i =>
    UInt8.ofNat (16 * hexDigit cs[2 * i]! + hexDigit cs[2 * i + 1]!)

def hexOfBytes (bs : List UInt8) : String :=
  String.join (bs.map fun b =>
    let s := String.ofList (Nat.toDigits 16 b.toNat)
    if s.length < 2 then "0" ++ s else s)

/-- `bytes` packed eight to a word in little-endian order, followed by bytes `0xA5` to the end of
the word after the message's last word. -/
def pack (bytes : List UInt8) : Array UInt64 :=
  let a := bytes.toArray
  (List.range ((a.size + 7) / 8 + 1)).toArray.map fun w =>
    (List.range 8).foldl (fun acc j =>
      let b := (a[8 * w + j]?.getD 0xA5).toUInt64
      acc ||| (b <<< (8 * j).toUInt64)) 0

/-- The first `k` bytes of words packed eight to a word in little-endian order. -/
def unpack (ws : List UInt64) (k : Nat) : List UInt8 :=
  (List.range k).map fun i => (ws[i / 8]!.toNat / 2 ^ (8 * (i % 8))).toUInt8

/-- Bytes as bits, most significant bit first, as FIPS 180-4 orders a message. -/
def toBits (bytes : List UInt8) : List Bool :=
  bytes.flatMap fun b => (List.range 8).reverse.map b.toNat.testBit

/-- The `k` bytes of `x`, most significant first. -/
def bytesOfNat (k x : Nat) : List UInt8 :=
  (List.range k).map fun i => (x / 2 ^ (8 * (k - 1 - i))).toUInt8

end TestSupport.Hashing.Packing
