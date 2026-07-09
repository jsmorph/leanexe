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
def u32lebU64 (n : UInt64) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut v := n
  for _ in [0:10] do
    let low := v % 128
    let rest := v / 128
    if rest == 0 then
      out := out.push low.toUInt8
      break
    out := out.push (low + 128).toUInt8
    v := rest
  return out

/-- Arithmetic shift right by seven over the two's-complement bits. -/
def sar7 (v : UInt64) : UInt64 :=
  if v &&& 9223372036854775808 == 0 then
    v >>> 7
  else
    (v >>> 7) ||| 18374686479671623680

/-- Signed LEB128 over the two's-complement bit pattern of an `i64`. -/
def s64lebU64 (n : UInt64) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut v := n
  for _ in [0:10] do
    let low := v &&& 127
    let rest := sar7 v
    if (rest == 0 && low &&& 64 == 0) ||
        (rest == 18446744073709551615 && low &&& 64 == 64) then
      out := out.push low.toUInt8
      break
    out := out.push (low + 128).toUInt8
    v := rest
  return out

end LeanExe.Wasm.Leb
