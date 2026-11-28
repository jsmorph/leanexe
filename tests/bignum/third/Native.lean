import Library.Numerics.Bignum.Third.Program
import Library.Numerics.Bignum.Spec

/-!
Evaluates the third iteration's divisions and printers in native Lean on the cases that
`check.mjs` writes, beside the first iteration's `natDivModChecked`, `intTDivModChecked`,
`intEDivModChecked`, and `intToText` and the specification, whose `Nat` and `Int` use GMP in the
runtime.  A case fails when the new function differs from either, and the script prints the new
function's result in the form in which `check.mjs` prints the module's, so that `run.sh` compares
the two files.  The first iteration's Algorithm D reads past the end of a dividend that is shorter
than the divisor, which the runtime reports on the standard error; the reads give 0, as the
specification of `xs[i]!` states, and the results are unaffected.
Usage: lake env lean --run tests/bignum/third/Native.lean cases.txt lean.txt
-/

open Library.Numerics.Bignum
open Library.Numerics.MultiPrecision (value)

def words (xs : Array UInt64) : String := "[" ++ ",".intercalate (xs.toList.map toString) ++ "]"
def flag (b : Bool) : String := if b then "1" else "0"
def wordsOf (s : String) : Array UInt64 :=
  if s.isEmpty then #[] else ((s.splitOn ",").map fun t => t.toNat!.toUInt64).toArray
def recOf (s : String) : BigInt :=
  match s.splitOn ":" with
  | [n, m] => ⟨n == "1", wordsOf m⟩
  | _ => ⟨false, #[]⟩

def divOut (r : UInt64 × BigInt × BigInt) : String :=
  toString r.1 ++ ":" ++ flag r.2.1.neg ++ ":" ++ words r.2.1.mag ++ ":" ++ flag r.2.2.neg ++ ":" ++
    words r.2.2.mag

def caseLine (line : String) : Except String String :=
  match line.splitOn "|" with
  | ["natDiv", a, b] =>
    let u := wordsOf a
    let v := wordsOf b
    let r := natDivModCheckedBZ u v
    if r != natDivModCheckedSpec (value u) (value v) then
      .error "natDivModCheckedBZ differs from the specification"
    else if r != natDivModChecked u v then .error "natDivModCheckedBZ differs from natDivModChecked"
    else .ok (toString r.1 ++ ":" ++ words r.2.1 ++ ":" ++ words r.2.2)
  | ["intDiv", a, b] =>
    let x := recOf a
    let y := recOf b
    let rt := intTDivModCheckedBZ x y
    let re := intEDivModCheckedBZ x y
    if rt != intTDivModCheckedSpec x.toInt y.toInt then
      .error "intTDivModCheckedBZ differs from the specification"
    else if rt != intTDivModChecked x y then .error "intTDivModCheckedBZ differs from intTDivModChecked"
    else if re != intEDivModCheckedSpec x.toInt y.toInt then
      .error "intEDivModCheckedBZ differs from the specification"
    else if re != intEDivModChecked x y then .error "intEDivModCheckedBZ differs from intEDivModChecked"
    else .ok (divOut rt ++ ";" ++ divOut re)
  | ["print", a] =>
    let u := wordsOf a
    let t := natToTextDC u
    let x : BigInt := ⟨u.size != 0, u⟩
    let tn := intToTextDC x
    if t != printSpec (value u : ℤ) then .error "natToTextDC differs from printSpec"
    else if t != intToText ⟨false, u⟩ then .error "natToTextDC differs from intToText"
    else if tn != printSpec x.toInt then .error "intToTextDC differs from printSpec"
    else if tn != intToText x then .error "intToTextDC differs from intToText"
    else .ok (words t ++ ";" ++ words tn)
  | _ => .error "unknown case"

def main (args : List String) : IO Unit := do
  let [casesPath, outPath] := args | throw (IO.userError "usage: Native.lean cases.txt lean.txt")
  let lines := (← IO.FS.lines casesPath).filter (· ≠ "")
  let mut out := #[]
  for l in lines do
    match caseLine l with
    | .ok r => out := out.push r
    | .error e => throw (IO.userError s!"{e}: {l.take 80}")
  IO.FS.writeFile outPath ("\n".intercalate out.toList ++ "\n")
  IO.println s!"native Lean: {lines.size} cases of the new functions equal to the first iteration's and to the specification"
