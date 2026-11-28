module

public import Demos.Scheme.Semantics.Machine

@[expose] public section

/-! The outcomes of a run of the reference semantics: the datum and the written form of a final
value, the text of each fault, and the bytes of an outcome, a status byte followed by text, as
[the profile](../profile.md) states them.  The executable interpreter writes the same bytes. -/

namespace Demos.Scheme.Semantics

open Numeric

mutual

/-- The datum that a value denotes, through at most `fuel` pairs on any path, or `none` for a
procedure, the unspecified value, or a circular structure. -/
def extern (s : State) : Nat → Val → Option Datum
  | 0, _ => none
  | fuel + 1, v =>
    match v with
    | .bool b => some (.bool b)
    | .int n => some (.int n)
    | .char c => some (.char c)
    | .sym x => some (.sym x)
    | .nil => some .nil
    | .str _ ls _ => some (.str (ls.map fun l => match s.read l with | .char c => c | _ => 0))
    | .pair a d _ =>
      match extern s fuel (s.read a), extern s fuel (s.read d) with
      | some x, some y => some (.pair x y)
      | _, _ => none
    | .vec _ ls _ => (externList s fuel (ls.map s.read)).map .vec
    | _ => none

def externList (s : State) : Nat → List Val → Option Datum
  | 0, _ => none
  | _ + 1, [] => some .nil
  | fuel + 1, v :: vs =>
    match extern s fuel v, externList s fuel vs with
    | some x, some y => some (.pair x y)
    | _, _ => none

end

mutual

/-- The written form of a value (§6.10.3), through at most `fuel` pairs on any path, with
`#<procedure>` and `#<unspecified>` for the objects without a standard representation (§3.3). -/
def writeVal (s : State) : Nat → Val → Option (List UInt8)
  | 0, _ => none
  | fuel + 1, v =>
    match v with
    | .bool b => some (if b then bytes "#t" else bytes "#f")
    | .int n => some (writeInt n)
    | .char c => some (writeChar c)
    | .sym x => some x
    | .nil => some (bytes "()")
    | .unspecified => some (bytes "#<unspecified>")
    | .undefined => some (bytes "#<undefined>")
    | .proc .. => some (bytes "#<procedure>")
    | .str _ ls _ => some (writeStr (ls.map fun l => match s.read l with | .char c => c | _ => 0))
    | .pair a d _ =>
      match writeVal s fuel (s.read a), writeTailVal s fuel (s.read d) with
      | some x, some y => some (40 :: x ++ y)
      | _, _ => none
    | .vec _ ls _ =>
      match ls with
      | [] => some (bytes "#()")
      | l :: rest =>
        match writeVal s fuel (s.read l), writeElemsVal s fuel (rest.map s.read) with
        | some x, some y => some (35 :: 40 :: x ++ y)
        | _, _ => none

/-- The written rest of a list after its first element, through the closing parenthesis. -/
def writeTailVal (s : State) : Nat → Val → Option (List UInt8)
  | 0, _ => none
  | _ + 1, .nil => some [41]
  | fuel + 1, .pair a d _ =>
    match writeVal s fuel (s.read a), writeTailVal s fuel (s.read d) with
    | some x, some y => some (32 :: x ++ y)
    | _, _ => none
  | fuel + 1, v => (writeVal s fuel v).map fun x => bytes " . " ++ x ++ [41]

/-- The written elements of a vector after its first, through the closing parenthesis. -/
def writeElemsVal (s : State) : Nat → List Val → Option (List UInt8)
  | 0, _ => none
  | _ + 1, [] => some [41]
  | fuel + 1, v :: vs =>
    match writeVal s fuel v, writeElemsVal s fuel vs with
    | some x, some y => some (32 :: x ++ y)
    | _, _ => none

end

def ReadError.text : ReadError → List UInt8
  | .incomplete => bytes "incomplete datum"
  | .unexpectedClose => bytes "unexpected )"
  | .badDot => bytes "misplaced dot"
  | .badHash => bytes "bad # syntax"
  | .badChar => bytes "unknown character name"
  | .badToken => bytes "invalid token"
  | .badByte => bytes "invalid byte"
  | .badString => bytes "bad string escape"

def SyntaxError.text : SyntaxError → List UInt8
  | .emptyCombination => bytes "empty combination"
  | .vector => bytes "vector as expression"
  | .improper => bytes "improper combination"
  | .keyword s => bytes "keyword as variable: " ++ s
  | .badForm s => bytes "bad form: " ++ s
  | .unsupported s => bytes "unsupported form: " ++ s
  | .duplicate s => bytes "duplicate variable: " ++ s
  | .duplicateDatum => bytes "duplicate case datum"
  | .definition => bytes "definition in expression context"
  | .misplaced s => bytes "misplaced keyword: " ++ s
  | .template => bytes "bad quasiquote template"

def RunError.text : RunError → List UInt8
  | .unbound s => bytes "unbound variable: " ++ s
  | .undefinedVariable => bytes "undefined variable"
  | .notProcedure => bytes "not a procedure"
  | .arity => bytes "wrong number of arguments"
  | .wrongType => bytes "wrong type of argument"
  | .immutable => bytes "immutable object"
  | .divideByZero => bytes "division by zero"
  | .index => bytes "index out of range"

def Numeric.Restriction.text : Restriction → List UInt8
  | .range => bytes "number out of range"
  | .notInteger => bytes "non-integer result"
  | .number => bytes "number outside the profile"

/-- The bytes of a fault: its status byte and its text. -/
def Fault.render : Fault → List UInt8
  | .read e pos => 1 :: e.text ++ bytes " at " ++ natDigits pos
  | .syntax e => 2 :: e.text
  | .error e => 3 :: e.text
  | .restriction r => 4 :: r.text

/-- The fuel of the writers and of `extern` for a state: more than the pairs of any path through
an acyclic structure. -/
def State.fuel (s : State) : Nat := s.store.length + 2

/-- The bytes of a final configuration: status 0 and the written value, or the fault's bytes. -/
def render : Config → Option (List UInt8)
  | .halt v s => (writeVal s s.fuel v).map (0 :: ·)
  | .fault f => some f.render
  | _ => none

/-- The datum of a final value. -/
def resultDatum : Config → Option Datum
  | .halt v s => extern s s.fuel v
  | _ => none

/-- The bytes of the run of a program for `n` rules, or `none` when the run has not ended. -/
def outcome (P : Profile) (n : Nat) (src : List UInt8) : Option (List UInt8) :=
  render (run P n (start P src))

end Demos.Scheme.Semantics
