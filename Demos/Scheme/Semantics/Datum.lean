module

@[expose] public section

/-! External representations of R4RS Scheme (§3.3, §7.1.2): the data that the reader produces
and that a quotation denotes, and their written form (§6.10.3).  A symbol is the list of its
ASCII bytes.  A vector holds its elements as a proper list, so that the type is an ordinary
inductive type with decidable equality. -/

namespace Demos.Scheme.Semantics

/-- The spelling of a symbol: its ASCII bytes.  The reader folds the letters of an identifier to
lower case (§2). -/
abbrev Sym := List UInt8

/-- The bytes of a string literal of Lean, for the spellings and texts of this semantics. -/
def bytes (s : String) : List UInt8 := s.toUTF8.toList

/-- A datum (§7.1.2).  `vec elems` holds the elements of a vector as the proper list `elems`. -/
inductive Datum where
  | bool (b : Bool)
  | int (n : Int)
  | char (c : UInt8)
  | str (s : List UInt8)
  | sym (s : Sym)
  | nil
  | pair (a d : Datum)
  | vec (elems : Datum)
  deriving DecidableEq, Repr, Inhabited

namespace Datum

/-- The list of the data `xs` ending in the tail `t`. -/
def ofList : List Datum → Datum → Datum
  | [], t => t
  | x :: xs, t => .pair x (ofList xs t)

/-- The proper list of the data `xs`. -/
def list (xs : List Datum) : Datum := ofList xs .nil

/-- The elements of a proper list, or `none` for any other datum. -/
def toList? : Datum → Option (List Datum)
  | .nil => some []
  | .pair a d => (toList? d).map (a :: ·)
  | _ => none

/-- Whether a datum is a pair, a string, or a vector, which denote locations (§3.4, §3.5). -/
def compound : Datum → Bool
  | .pair .. | .str _ | .vec _ => true
  | _ => false

end Datum

/-- The decimal digits of `n`, at most `fuel` of them. -/
def natDigitsAux : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    if n < 10 then (48 + n).toUInt8 :: acc
    else natDigitsAux fuel (n / 10) ((48 + n % 10).toUInt8 :: acc)

/-- The decimal digits of `n`. -/
def natDigits (n : Nat) : List UInt8 := natDigitsAux (n + 1) n []

/-- The written form of an integer: its decimal digits, after a minus sign when negative. -/
def writeInt (n : Int) : List UInt8 :=
  if n < 0 then 45 :: natDigits n.natAbs else natDigits n.natAbs

/-- The written form of a character (§6.6): `#\space`, `#\newline`, or `#\` and the
character. -/
def writeChar (c : UInt8) : List UInt8 :=
  if c == 32 then bytes "#\\space"
  else if c == 10 then bytes "#\\newline"
  else [35, 92, c]

/-- The written form of a string (§6.7): its characters between double quotes, with `\` before
each double quote and backslash. -/
def writeStr (s : List UInt8) : List UInt8 :=
  34 :: (s.flatMap fun c => if c == 34 || c == 92 then [92, c] else [c]) ++ [34]

namespace Datum

mutual

/-- The written form of a datum (§6.10.3). -/
def write : Datum → List UInt8
  | .bool b => if b then bytes "#t" else bytes "#f"
  | .int n => writeInt n
  | .char c => writeChar c
  | .str s => writeStr s
  | .sym s => s
  | .nil => bytes "()"
  | .pair a d => 40 :: write a ++ writeTail d
  | .vec elems => 35 :: 40 :: writeElems elems

/-- The written form of the rest of a list after its first element, through its closing
parenthesis. -/
def writeTail : Datum → List UInt8
  | .nil => [41]
  | .pair a d => 32 :: write a ++ writeTail d
  | d => bytes " . " ++ write d ++ [41]

/-- The written elements of a vector's list, through the closing parenthesis. -/
def writeElems : Datum → List UInt8
  | .pair a d => write a ++ writeTail d
  | _ => [41]

end

end Datum

end Demos.Scheme.Semantics
