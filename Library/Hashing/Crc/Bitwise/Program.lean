/-! CRC-32 of `Library.Hashing.Crc.Spec` by eight steps of the division for each byte, with no
table.  The functions use no linear memory, global, or floating point, so a program of the
Cortex-M7 back end that calls them has no area.  A register holds the remainder in its low 32 bits
as `Library.Hashing.Crc.byteStep` holds it, bit `i` the coefficient of `x^(31 - i)`, so a step of
the division shifts the register right by one and XORs CRC-32's generator in the same order,
`0xEDB88320`, when the bit shifted out is 1.  `crc32Reg` XORs a byte into the register's low eight
bits and takes eight steps.  `crc32Byte` and `crc32Word` take and return a CRC as zlib's `crc32`
does: they start from the complement of the low 32 bits of the CRC argument, which is 32 ones for
the CRC of no bytes, and complement the final register. -/

namespace Library.Hashing.Crc.Bitwise

/-- One step of the division: the register `r` shifted right by one and XORed with `0xEDB88320`
when its low bit is 1.  The product of the low bit and the generator selects the XOR without a
branch. -/
@[inline] def bitStep (r : UInt64) : UInt64 := (r >>> 1) ^^^ ((r &&& 1) * 0xEDB88320)

/-- The register after the byte in the low eight bits of `b`, from the register `r`. -/
def crc32Reg (r b : UInt64) : UInt64 :=
  let r := r ^^^ (b &&& 0xFF)
  let r := bitStep r
  let r := bitStep r
  let r := bitStep r
  let r := bitStep r
  let r := bitStep r
  let r := bitStep r
  let r := bitStep r
  bitStep r

/-- The register after the byte `b` when `k < n`, and `r` otherwise. -/
@[inline] def regIf (k n r b : UInt64) : UInt64 := if k < n then crc32Reg r b else r

/-- CRC-32 of a prefix followed by the byte in the low eight bits of `b`, from CRC-32 `crc` of the
prefix in its low 32 bits. -/
def crc32Byte (crc b : UInt64) : UInt64 :=
  crc32Reg ((crc ^^^ 0xFFFFFFFF) &&& 0xFFFFFFFF) b ^^^ 0xFFFFFFFF

/-- CRC-32 of a prefix followed by the first `n` bytes of `w`, at most eight, from its most
significant byte, from CRC-32 `crc` of the prefix in its low 32 bits.  A record decoded into words
most significant byte first, as `LeanExe.Requests.decode` decodes one, passes each word with the
count of its bytes in the record. -/
def crc32Word (crc w n : UInt64) : UInt64 :=
  let r := (crc ^^^ 0xFFFFFFFF) &&& 0xFFFFFFFF
  let r := regIf 0 n r (w >>> 56)
  let r := regIf 1 n r (w >>> 48)
  let r := regIf 2 n r (w >>> 40)
  let r := regIf 3 n r (w >>> 32)
  let r := regIf 4 n r (w >>> 24)
  let r := regIf 5 n r (w >>> 16)
  let r := regIf 6 n r (w >>> 8)
  let r := regIf 7 n r w
  r ^^^ 0xFFFFFFFF

end Library.Hashing.Crc.Bitwise
