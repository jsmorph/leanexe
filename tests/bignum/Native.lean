import Library.Numerics.Bignum.Spec

/-!
Evaluates the specification in native Lean, whose `Nat` and `Int` use GMP in the runtime, on the
cases that `check.mjs` writes, and prints each result in the form in which `check.mjs` prints the
module's.  The program's own Lean functions are not run here: MultiPrecision's loops read past the
end of the shorter operand, whose default element is 0, and the Lean runtime reports every such
read, which slows a run of this size; the equations of the proofs relate the program to the
specification, and `TestSupport.Bignum.Cases` evaluates the program on cases of the divisions that
the module does not export.
Usage: lake env lean --run tests/bignum/Native.lean cases.txt lean.txt
-/

open Library.Numerics.Bignum

def words (xs : Array UInt64) : String := "[" ++ ",".intercalate (xs.toList.map toString) ++ "]"
def recS (x : BigInt) : String := (if x.neg then "1" else "0") ++ ":" ++ words x.mag
def flag (b : Bool) : String := if b then "1" else "0"
def wordsOf (s : String) : Array UInt64 :=
  if s.isEmpty then #[] else ((s.splitOn ",").map fun t => t.toNat!.toUInt64).toArray
def nat (s : String) : Nat := s.toNat!
def int (s : String) : Int := s.toInt!

def specLine (line : String) : String :=
  match line.splitOn "|" with
  | ["natCmp", a, b] => toString (cmpSpec (nat a) (nat b))
  | ["natAdd", a, b] => words (limbsOf (nat a + nat b))
  | ["natSub", a, b] => let r := natSubSpec (nat a) (nat b); flag r.1 ++ ";" ++ words r.2
  | ["natMul", a, b] => words (limbsOf (nat a * nat b))
  | ["natDivMod", a, b] =>
    let r := natDivModCheckedSpec (nat a) (nat b)
    toString r.1 ++ ";" ++ words r.2.1 ++ ";" ++ words r.2.2
  | ["natTrim", w] =>
    words (limbsOf (Library.Numerics.MultiPrecision.value (wordsOf w)))
  | ["intNeg", a] => recS (.ofInt (-int a))
  | ["intCmp", a, b] => toString (cmpSpec (int a) (int b))
  | ["intAdd", a, b] => recS (.ofInt (int a + int b))
  | ["intSub", a, b] => recS (.ofInt (int a - int b))
  | ["intMul", a, b] => recS (.ofInt (int a * int b))
  | ["intTDivModChecked", a, b] =>
    let r := intTDivModCheckedSpec (int a) (int b)
    toString r.1 ++ ";" ++ recS r.2.1 ++ ";" ++ recS r.2.2
  | ["intEDivModChecked", a, b] =>
    let r := intEDivModCheckedSpec (int a) (int b)
    toString r.1 ++ ";" ++ recS r.2.1 ++ ";" ++ recS r.2.2
  | ["intToText", a] => words (printSpec (int a))
  | ["intOfText", s] => let r := readSpec (wordsOf s); flag r.1 ++ ";" ++ recS r.2
  | ["textNeg", s] => let r := textNegSpec (wordsOf s); toString r.1 ++ ";" ++ words r.2
  | ["textCmp", s, t] => let r := textCmpSpec (wordsOf s) (wordsOf t); toString r.1 ++ ";" ++ toString r.2
  | [op, s, t] =>
    let f := match op with
      | "textAdd" => textAddSpec | "textSub" => textSubSpec | "textMul" => textMulSpec
      | "textTDiv" => textTDivSpec | "textTMod" => textTModSpec | "textEDiv" => textEDivSpec
      | _ => textEModSpec
    let r := f (wordsOf s) (wordsOf t)
    toString r.1 ++ ";" ++ words r.2
  | _ => "unknown"

def main (args : List String) : IO Unit := do
  let [casesPath, outPath] := args | throw (IO.userError "usage: Native.lean cases.txt lean.txt")
  let lines := (← IO.FS.lines casesPath).filter (· ≠ "")
  let out := lines.map specLine
  IO.FS.writeFile outPath ("\n".intercalate out.toList ++ "\n")
  IO.println s!"native Lean: {lines.size} cases evaluated by the specification"

