/-!
# LEB128 encoding

The variable-length integer encodings used throughout the WASM binary
format, written inside the LeanExe-accepted subset so the compiler's own
encoder can compile to a verified artifact.  `LeanExe/Wasm/Binary.lean`
uses these definitions for all native emission, so the shipped compiler
and the self-compiled artifact run the same code.
-/

namespace LeanExe.Wasm.Leb

/-- Unsigned LEB128.  Ten groups of seven bits cover a `UInt64`. -/
def u32lebFuel : Nat → UInt64 → ByteArray → ByteArray
  | 0, _, out => out
  | fuel + 1, v, out =>
      let low := v % 128
      let rest := v / 128
      if rest == 0 then
        out.push low.toUInt8
      else
        u32lebFuel fuel rest (out.push (low + 128).toUInt8)

def u32lebU64 (n : UInt64) : ByteArray :=
  u32lebFuel 10 n ByteArray.empty

/-- Arithmetic shift right by seven over the two's-complement bits. -/
def sar7 (v : UInt64) : UInt64 :=
  if v &&& 9223372036854775808 == 0 then
    v >>> 7
  else
    (v >>> 7) ||| 18374686479671623680

/-- Signed LEB128 over the two's-complement bit pattern of an `i64`. -/
def s64lebFuel : Nat → UInt64 → ByteArray → ByteArray
  | 0, _, out => out
  | fuel + 1, v, out =>
      let low := v &&& 127
      let rest := sar7 v
      if (rest == 0 && low &&& 64 == 0) ||
          (rest == 18446744073709551615 && low &&& 64 == 64) then
        out.push low.toUInt8
      else
        s64lebFuel fuel rest (out.push (low + 128).toUInt8)

def s64lebU64 (n : UInt64) : ByteArray :=
  s64lebFuel 10 n ByteArray.empty

/-- A length-prefixed byte vector. -/
def byteVecBytes (bytes : ByteArray) : ByteArray :=
  u32lebU64 (UInt64.ofNat bytes.size) ++ bytes

/-- A length-prefixed vector of encoded items. -/
def vecBytes (items : Array ByteArray) : ByteArray := Id.run do
  let mut out := u32lebU64 (UInt64.ofNat items.size)
  for item in items do
    out := out ++ item
  return out

/-- A length-prefixed vector of unsigned LEB128 values. -/
def u32VecBytes (values : Array UInt64) : ByteArray := Id.run do
  let mut out := u32lebU64 (UInt64.ofNat values.size)
  for value in values do
    out := out ++ u32lebU64 value
  return out

/-- A section: one id byte, then the length-prefixed payload. -/
def sectionBytes (id : UInt64) (payload : ByteArray) : ByteArray :=
  (ByteArray.empty.push id.toUInt8) ++
    u32lebU64 (UInt64.ofNat payload.size) ++ payload

end LeanExe.Wasm.Leb
