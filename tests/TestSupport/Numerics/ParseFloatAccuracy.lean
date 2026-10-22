import Library.Numerics.Decimal.ParseFloat.Compiled
import Library.Numerics.Decimal.Shared.StrconvDecode

/-! A native check of `Library.Numerics.Decimal.ParseFloat.ParseFloat.parse64` and `parse32` on the cases of
`data/strconv/parse-cases.txt`, which `tools/strconv/parse_cases.py` selects and computes: lines of
Nigel Tao's parse-number-fxx-test-data, Paxson's hard inputs, strings next to midpoints with up to
1,100 digits, and strings for every production and rejection of the grammar.  Each result must
equal the expected words of the file, computed in Python with exact rationals, and, for an
accepted string, a second reference computed here: `Library.Numerics.Decimal.Shared.StrconvDecode.decode`, which
`derives_iff_decode` proves equal to the grammar, gives the number, and Talos's
`roundRationalMagnitude`, which `Library.Numerics.Decimal.Shared.StrconvRational.rational64` and `rational32` prove equal to the
references, rounds it.  The check exits with an error at the first difference.  Run with
`lake env lean --run`. -/

namespace TestSupport.Numerics.ParseFloatAccuracy
open Library.Numerics.Decimal.Shared.StrconvGrammar

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

def parseHex (s : String) : Nat := s.foldl (fun v c => 16 * v + hexDigit c) 0

def bytesOfHex (s : String) : List UInt8 :=
  let cs := s.toList
  (List.range (cs.length / 2)).map fun i =>
    UInt8.ofNat (16 * hexDigit cs[2 * i]! + hexDigit cs[2 * i + 1]!)

/-- The number of decimal digits of `d > 0`. -/
def digits (d : Nat) : Nat := (Nat.toDigits 10 d).length

/-- The reference magnitude word of a finite decimal or hexadecimal number: `rr` rounds a rational
in units of the least subnormal, `nu` is the exponent of that unit, and `inf` the word of
infinity.  Values beyond `10 ^ 400` or below `10 ^ -400` saturate. -/
def refMag (rr : Nat → Nat → UInt64) (nu : Nat) (inf : UInt64) (hex : Bool) (d : Nat) (e : Int) :
    UInt64 :=
  if d = 0 then 0
  else if hex then
    if e > 2000 then inf
    else if e < -2000 - 4 * (digits d : Int) then 0
    else rr (d * 2 ^ (e + nu).toNat) (2 ^ (-(e + nu)).toNat)
  else if e + digits d > 400 then inf
  else if e + digits d < -400 then 0
  else rr (d * 10 ^ e.toNat * 2 ^ nu) (10 ^ (-e).toNat)

def ref64 (n : Num) : UInt64 :=
  let sign (neg : Bool) (w : UInt64) := if neg then w ||| 0x8000000000000000 else w
  match n with
  | .nan => 0x7FF8000000000000
  | .inf neg => sign neg 0x7FF0000000000000
  | .dec neg d e => sign neg (refMag (Wasm.IEEE64.roundRationalMagnitude false) 1074
      0x7FF0000000000000 false d e)
  | .hex neg d e => sign neg (refMag (Wasm.IEEE64.roundRationalMagnitude false) 1074
      0x7FF0000000000000 true d e)

def ref32 (n : Num) : UInt64 :=
  let sign (neg : Bool) (w : UInt64) := if neg then w ||| 0x80000000 else w
  let rr (a b : Nat) : UInt64 := (Wasm.IEEE32.roundRationalMagnitude false a b).toUInt64
  match n with
  | .nan => 0x7FC00000
  | .inf neg => sign neg 0x7F800000
  | .dec neg d e => sign neg (refMag rr 149 0x7F800000 false d e)
  | .hex neg d e => sign neg (refMag rr 149 0x7F800000 true d e)

def main : IO Unit := do
  let text ← IO.FS.readFile "data/strconv/parse-cases.txt"
  let mut count := 0
  for row in text.splitOn "\n" do
    if row.isEmpty then continue
    let f := (row.splitOn " ").toArray
    let general := f[0]! == "g"
    let ok := f[1]! == "1"
    let w64 := UInt64.ofNat (parseHex f[2]!)
    let w32 := UInt64.ofNat (parseHex f[4]!)
    let bytes := bytesOfHex (f[5]?.getD "")
    let s := words bytes
    let r64 := Library.Numerics.Decimal.ParseFloat.ParseFloat.parse64 general s
    let r32 := Library.Numerics.Decimal.ParseFloat.ParseFloat.parse32 general s
    let want64 := if ok then (true, w64) else (false, 0)
    let want32 := if ok then (true, w32) else (false, 0)
    if r64 != want64 then
      throw (IO.userError s!"parse64 {row}: {r64.1} {r64.2.toNat}")
    if r32 != want32 then
      throw (IO.userError s!"parse32 {row}: {r32.1} {r32.2.toNat}")
    match Library.Numerics.Decimal.Shared.StrconvDecode.decode general bytes with
    | some n =>
      if !ok || ref64 n != w64 || ref32 n != w32 then
        throw (IO.userError s!"reference {row}")
    | none =>
      if ok then throw (IO.userError s!"decode rejects {row}")
    count := count + 1
  IO.println s!"{count} cases: parse64 and parse32 equal the expected words and the references"

end TestSupport.Numerics.ParseFloatAccuracy

def main : IO Unit := TestSupport.Numerics.ParseFloatAccuracy.main
