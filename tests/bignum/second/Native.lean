import Library.Numerics.Bignum.Second.Spec
import Library.Numerics.Bignum.Second.Program

/-!
Evaluates the second iteration's products and readers in native Lean on the cases that
`check.mjs` writes, beside the first iteration's `natMul`, `intMul`, and `intOfText` and the
specification, whose `Nat` and `Int` use GMP in the runtime.  A case fails when the new function
differs from either, and the script prints the new function's result in the form in which
`check.mjs` prints the module's, so that `run.sh` compares the two files.
Usage: lake env lean --run tests/bignum/second/Native.lean cases.txt lean.txt
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

def caseLine (line : String) : Except String String :=
  match line.splitOn "|" with
  | ["natMul", a, b] =>
    let u := wordsOf a
    let v := wordsOf b
    let r := natMulKara u v
    if r != limbsOf (value u * value v) then .error "natMulKara differs from limbsOf of the product"
    else if r != natMul u v then .error "natMulKara differs from natMul"
    else .ok (words r)
  | ["intMul", a, b] =>
    let x := recOf a
    let y := recOf b
    let r := intMulKara x y
    if r != BigInt.ofInt (x.toInt * y.toInt) then .error "intMulKara differs from ofInt of the product"
    else if r != intMul x y then .error "intMulKara differs from intMul"
    else .ok (flag r.neg ++ ":" ++ words r.mag)
  | ["read", s] =>
    let ws := wordsOf s
    let r := intOfTextDC ws
    let n := natOfTextDC ws
    if r != readSpec ws then .error "intOfTextDC differs from readSpec"
    else if r != intOfText ws then .error "intOfTextDC differs from intOfText"
    else if n != natReadSpec ws then .error "natOfTextDC differs from natReadSpec"
    else .ok (flag r.1 ++ ":" ++ flag r.2.neg ++ ":" ++ words r.2.mag ++ ";" ++ flag n.1 ++ ":" ++
      words n.2)
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
