module

public import Demos.Scheme.Semantics.Outcome
public import Demos.Scheme.Machine.Codes

@[expose] public section

/-! The reference outcomes of the executable interpreter's modes 0 and 1, from the reference
semantics: the data that the reference reader reads, each written and followed by a line feed, and
the forms that the reference expander gives each datum, in the tagged form of
`Demos.Scheme.Machine.convStep`, each followed by a line feed.  The code of a standard procedure is
its machine code, which `Demos.Scheme.Machine.primList` gives its name. -/

namespace TestSupport.Scheme.Oracle

open Demos.Scheme.Semantics Demos.Scheme.Machine

/-- The machine code of a standard procedure, through its name. -/
def primCodeOf (p : Prim) : Nat :=
  match (primNames.find? (·.2 == p)) with
  | some (name, _) => ((primList.find? fun (n, _) => bytes n == name).map (·.2.toNat)).getD 0
  | none => 0

/-- The bytes of a list of byte strings, separated by spaces, in parentheses. -/
def paren (xs : List (List UInt8)) : List UInt8 := 40 :: (List.intersperse [32] xs).flatten ++ [41]

def numText (n : Nat) : List UInt8 := natDigits n

def constText : Const → List UInt8
  | .datum d => paren [numText 0, Datum.write d]
  | .lit _ => paren [numText 0]
  | .undefined => paren [numText 0, bytes "#<undefined>"]
  | .unspecified => paren [numText 0, bytes "#<unspecified>"]
  | .prim p => paren [numText 9, numText (primCodeOf p)]

def varText (scope : List Var) (x : Var) (local_ global : Nat) : List (List UInt8) :=
  match scope.idxOf? x with
  | some i => [numText local_, numText i]
  | none =>
    match x with
    | .id s => [numText global, s]
    | .temp n => [numText global, bytes "temp" ++ natDigits n]

mutual

/-- The tagged form of a core expression in a scope whose first variable has position 0. -/
def exprText (scope : List Var) : Expr → List UInt8
  | .const k => constText k
  | .var x => paren (varText scope x 1 2)
  | .app f args => paren (numText 8 :: exprText scope f :: exprsText scope args)
  | .lam fs r body last =>
    let scope' := fs ++ r.toList ++ scope
    paren ([numText 7, numText fs.length, if r.isSome then bytes "#t" else bytes "#f"] ++
      exprsText scope' body ++ [exprText scope' last])
  | .ite c t e => paren [numText 6, exprText scope c, exprText scope t, exprText scope e]
  | .set x e => paren (varText scope x 3 4 ++ [exprText scope e])

def exprsText (scope : List Var) : List Expr → List (List UInt8)
  | [] => []
  | e :: es => exprText scope e :: exprsText scope es

end

def topText : TopForm → List UInt8
  | .expr e => exprText [] e
  | .define x e => paren [numText 5, x, exprText [] e]

/-- The reference outcome of mode 0. -/
def readOutcome (src : List UInt8) : List UInt8 :=
  match readProgram Numeric.fixnum src with
  | .ok ds => 0 :: ds.flatMap fun d => Datum.write d ++ [10]
  | .error (.error e pos) => (Fault.read e pos).render
  | .error (.restriction r) => (Fault.restriction r).render

/-- The texts of the forms of the data, or the first syntax error. -/
def expandTexts : List Datum → Except SyntaxError (List UInt8)
  | [] => .ok []
  | d :: ds =>
    match expandTop d, expandTexts ds with
    | .ok tfs, .ok rest => .ok (tfs.flatMap (fun tf => topText tf ++ [10]) ++ rest)
    | .error e, _ => .error e
    | _, .error e => .error e

/-- The reference outcome of mode 1. -/
def expandOutcome (src : List UInt8) : List UInt8 :=
  match readProgram Numeric.fixnum src with
  | .ok ds =>
    match expandTexts ds with
    | .ok t => 0 :: t
    | .error e => (Fault.syntax e).render
  | .error (.error e pos) => (Fault.read e pos).render
  | .error (.restriction r) => (Fault.restriction r).render

end TestSupport.Scheme.Oracle
