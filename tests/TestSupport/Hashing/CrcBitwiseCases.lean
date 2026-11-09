import Library.Hashing.Crc.Program
import TestSupport.Hashing.Packing

/-! The cases of the module `crcBitwise`.  The calls of `data/hashing/crc/bitwise.txt` carry the
results that `zlib.crc32` gives: `crc32Reg` from registers below 2^32, and `crc32Byte` and
`crc32Word` from CRC arguments with and without bits above the low 32, bytes with bits above the
low eight, and byte counts from 0 to beyond 8, among them the two words of the check string
`123456789`.  The calls of `crc32Reg` from registers with bits above the low 32 carry the result of
the table program's step `Library.Hashing.Crc.byteStep crc32Table`.  A case requires that the call
allocate nothing. -/

namespace TestSupport.Hashing.CrcBitwiseCases

open Library.Hashing.Crc TestSupport.Hashing.Packing

/-- The value of hexadecimal digits. -/
def hexValue (s : String) : Nat := s.foldl (fun acc c => 16 * acc + hexDigit c) 0

def line (export_ args : String) (result : Nat) : IO Unit :=
  IO.println s!"crcBitwise|{export_}|i64|{args}|{result}|0|0"

def cases : IO Unit := do
  let text ← IO.FS.readFile "data/hashing/crc/bitwise.txt"
  for l in text.splitOn "\n" do
    if l.isEmpty || l.startsWith "#" then continue
    match l.splitOn " " with
    | ["reg", r, b, v] => line "crc32Reg" s!"i64:{hexValue r} i64:{hexValue b}" (hexValue v)
    | ["byte", c, b, v] => line "crc32Byte" s!"i64:{hexValue c} i64:{hexValue b}" (hexValue v)
    | ["word", c, w, n, v] =>
      line "crc32Word" s!"i64:{hexValue c} i64:{hexValue w} i64:{hexValue n}" (hexValue v)
    | _ => throw <| IO.userError s!"bitwise.txt: malformed line {l}"
  for r in [(0x100000000 : UInt64), 0xFFFFFFFFFFFFFFFF, 0x123456789ABCDEF0, 0x8000000000000000] do
    for b in [(0 : UInt64), 0x5A, 0xFF, 0xFFFFFFFFFFFFFF00] do
      line "crc32Reg" s!"i64:{r} i64:{b}" (byteStep crc32Table r b).toNat

end TestSupport.Hashing.CrcBitwiseCases
