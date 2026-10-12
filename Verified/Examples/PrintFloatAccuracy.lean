import Verified.Examples.PrintFloat
import Verified.Examples.ParseFloat
import Verified.Examples.StrconvRound

/-! A native check of `PrintFloat.print64`, `print64Ecma`, `print32`, and `print32Ecma` on the
cases of `data/strconv/print-cases.txt`, which `tools/strconv/print_cases.py` selects and computes
by a search over the number of significant digits with exact rationals, and for binary64 checks
against Python's `repr`.  Each printed string must equal the expected one, and both strings must
read back through `ParseFloat.parse64` (or `parse32`) in the general grammar as the word, with
every NaN read as the canonical NaN; a finite word's strings must also be numbers of RFC 8259's
grammar.  The check exits with an error at the first difference.  Run with
`lake env lean --run`. -/

namespace Verified.Examples.PrintFloatAccuracy

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

def parseHex (s : String) : Nat := s.foldl (fun v c => 16 * v + hexDigit c) 0

def wordsOf (s : String) : Array UInt64 := (s.toList.map fun c => c.toNat.toUInt64).toArray

def render (a : Array UInt64) : String := String.ofList (a.toList.map fun w => Char.ofNat w.toNat)

def main : IO Unit := do
  let text ← IO.FS.readFile "data/strconv/print-cases.txt"
  let mut count := 0
  for row in text.splitOn "\n" do
    if row.isEmpty then continue
    let f := (row.splitOn " ").toArray
    let bits := f[0]!
    let w := UInt64.ofNat (parseHex f[1]!)
    let sci := wordsOf f[2]!
    let ecma := wordsOf f[3]!
    let finite := f[2]! != "NaN" && f[2]! != "Infinity" && f[2]! != "-Infinity"
    if bits == "64" then
      let a := PrintFloat.print64 w
      let b := PrintFloat.print64Ecma w
      if a != sci then throw (IO.userError s!"print64 {row}: {render a}")
      if b != ecma then throw (IO.userError s!"print64Ecma {row}: {render b}")
      let want := (true, StrconvRound.canon64 w)
      if ParseFloat.parse64 true a != want || ParseFloat.parse64 true b != want then
        throw (IO.userError s!"parse64 of print64 {row}")
      if finite && ((ParseFloat.parse64 false a).1 != true || (ParseFloat.parse64 false b).1 != true) then
        throw (IO.userError s!"RFC 8259 {row}")
    else
      let a := PrintFloat.print32 w
      let b := PrintFloat.print32Ecma w
      if a != sci then throw (IO.userError s!"print32 {row}: {render a}")
      if b != ecma then throw (IO.userError s!"print32Ecma {row}: {render b}")
      let want := (true, (StrconvRound.canon32 w.toUInt32).toUInt64)
      if ParseFloat.parse32 true a != want || ParseFloat.parse32 true b != want then
        throw (IO.userError s!"parse32 of print32 {row}")
      if finite && ((ParseFloat.parse32 false a).1 != true || (ParseFloat.parse32 false b).1 != true) then
        throw (IO.userError s!"RFC 8259 {row}")
    count := count + 1
  IO.println s!"{count} cases: the printers equal the expected strings, which read back as the words"

end Verified.Examples.PrintFloatAccuracy

def main : IO Unit := Verified.Examples.PrintFloatAccuracy.main
