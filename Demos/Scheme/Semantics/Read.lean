module

public import Demos.Scheme.Semantics.Datum
public import Demos.Scheme.Semantics.Numeric

@[expose] public section

/-! The reference reader: the bytes of a program to the data of §7.1.2, by the lexical syntax of
§7.1.1 and the numerals of §6.5.4, under the profile's choices.  The reader is a recursive
descent with a fuel that the input's length bounds, since each call consumes a byte.  An error
names its kind and the byte offset at which the reader detects it, and the offset of an
incomplete datum is the input's length.

Identifiers are folded to lower case (§2).  Whitespace is space, line feed, tab, carriage return,
and form feed (§2.2).  A token that begins with a digit, with `+`, `-`, or `.` and is no peculiar
identifier, or with `#` and a radix or exactness letter, is a numeral.  A numeral of the form
prefix, optional sign, and digits of its radix denotes an exact integer, unless its prefix is
`#i`.  Any other numeral whose bytes are among the bytes of R4RS's numerals for its radix denotes
a number outside the profile, an implementation restriction (§6.5.3), and a numeral with any
other byte is an invalid token. -/

namespace Demos.Scheme.Semantics

open Numeric

/-- The read errors. -/
inductive ReadError where
  /-- The input ends inside a datum. -/
  | incomplete
  /-- A `)` where a datum is expected. -/
  | unexpectedClose
  /-- A `.` other than one before the last datum of a list. -/
  | badDot
  /-- A `#` followed by no syntax of §7.1.1. -/
  | badHash
  /-- A `#\` followed by a name other than `space` and `newline`. -/
  | badChar
  /-- A token that is neither an identifier, a numeral, nor a dot. -/
  | badToken
  /-- A byte above 127 outside a comment, or a control byte other than whitespace outside a
  comment, a string, and a character. -/
  | badByte
  /-- A `\` in a string followed by a byte other than `"` and `\`. -/
  | badString
  deriving DecidableEq, Repr

/-- The failures of the reader: a read error at an offset, or a numeral outside the profile. -/
inductive ReadFault where
  | error (e : ReadError) (pos : Nat)
  | restriction (r : Restriction)
  deriving DecidableEq, Repr

/-- Whitespace (§2.2). -/
def isWhite (c : UInt8) : Bool := c == 32 || c == 10 || c == 9 || c == 13 || c == 12

/-- Delimiters (§7.1.1): whitespace, parentheses, the double quote, and the semicolon. -/
def isDelimiter (c : UInt8) : Bool := isWhite c || c == 40 || c == 41 || c == 34 || c == 59

/-- A byte that the profile excludes outside comments: a control byte other than whitespace, or a
byte of 127 or above. -/
def isBadByte (c : UInt8) : Bool := (c < 32 && !isWhite c) || c ≥ 127

/-- The byte with an upper-case ASCII letter folded to lower case. -/
def fold (c : UInt8) : UInt8 := if 65 ≤ c && c ≤ 90 then c + 32 else c

def isLetter (c : UInt8) : Bool := 97 ≤ fold c && fold c ≤ 122

def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57

/-- The special initials of §7.1.1: `! $ % & * / : < = > ? ~ _ ^`. -/
def isSpecialInitial (c : UInt8) : Bool :=
  c == 33 || c == 36 || c == 37 || c == 38 || c == 42 || c == 47 || c == 58 || c == 60 ||
    c == 61 || c == 62 || c == 63 || c == 126 || c == 95 || c == 94

def isInitial (c : UInt8) : Bool := isLetter c || isSpecialInitial c

/-- The subsequents of §7.1.1: initials, digits, and `. + -`. -/
def isSubsequent (c : UInt8) : Bool := isInitial c || isDigit c || c == 46 || c == 43 || c == 45

/-- The value of a digit in radix 16, or 16 for a byte that is no digit. -/
def digitValue (c : UInt8) : Nat :=
  if isDigit c then (c - 48).toNat
  else if 97 ≤ fold c && fold c ≤ 102 then (fold c - 87).toNat
  else 16

/-- Whether a byte occurs in R4RS's numerals of radix `r` (§7.1.1): a digit of the radix, `#`,
`.`, `/`, `+`, `-`, `@`, or one of the letters `e s f d l i`. -/
def isNumeralByte (r : Nat) (c : UInt8) : Bool :=
  digitValue c < r || c == 35 || c == 46 || c == 47 || c == 43 || c == 45 || c == 64 ||
    fold c == 101 || fold c == 115 || fold c == 102 || fold c == 100 || fold c == 108 ||
    fold c == 105

/-- The bytes of a token: the bytes before the next delimiter or the end. -/
def takeToken : List UInt8 → List UInt8 × List UInt8
  | [] => ([], [])
  | c :: cs => if isDelimiter c then ([], c :: cs) else
    let (t, rest) := takeToken cs
    (c :: t, rest)

/-- The offset within `t` of its first excluded byte, if it has one. -/
def firstBad : List UInt8 → Option Nat
  | [] => none
  | c :: cs => if isBadByte c then some 0 else (firstBad cs).map (· + 1)

/-- The input after whitespace and comments.  `comment` holds within a comment. -/
def skipAtmosphere : Bool → Nat → List UInt8 → Nat × List UInt8
  | _, p, [] => (p, [])
  | true, p, c :: cs => skipAtmosphere (c != 10) (p + 1) cs
  | false, p, c :: cs =>
    if isWhite c then skipAtmosphere false (p + 1) cs
    else if c == 59 then skipAtmosphere true (p + 1) cs
    else (p, c :: cs)

/-- The digits of an unsigned integer in radix `r`, most significant first, as a number. -/
def digitsValue (r : Nat) : List UInt8 → Option Nat
  | [] => none
  | [c] => if digitValue c < r then some (digitValue c) else none
  | c :: cs => if digitValue c < r then
      (digitsValue r cs).map (digitValue c * r ^ cs.length + ·) else none

/-- The prefixes of a numeral (§7.1.1): its radix, its exactness, `true` for `#e` and `false`
for `#i`, and the bytes after them, or `none` for a repeated or unknown prefix. -/
def numeralPrefix : Option Nat → Option Bool → List UInt8 → Option (Nat × Option Bool × List UInt8)
  | r, e, 35 :: c :: rest =>
    let k := fold c
    if k == 98 || k == 111 || k == 100 || k == 120 then
      if r.isSome then none
      else numeralPrefix (some (if k == 98 then 2 else if k == 111 then 8 else if k == 100 then 10
        else 16)) e rest
    else if k == 101 || k == 105 then
      if e.isSome then none else numeralPrefix r (some (k == 101)) rest
    else none
  | r, e, body => some (r.getD 10, e, body)

/-- The integer that the digits of a signed body denote in radix `r`. -/
def signedValue (r : Nat) : List UInt8 → Option Int
  | 43 :: ds => (digitsValue r ds).map Int.ofNat
  | 45 :: ds => (digitsValue r ds).map fun n => -Int.ofNat n
  | ds => (digitsValue r ds).map Int.ofNat

/-- The datum of a numeral token that begins at offset `p`. -/
def readNumeral (P : Profile) (p : Nat) (t : List UInt8) : Except ReadFault Datum :=
  match numeralPrefix none none t with
  | none => .error (.error .badToken p)
  | some (r, e, body) =>
    if body.isEmpty then .error (.error .badToken p)
    else match signedValue r body with
      | some n =>
        if e == some false then .error (.restriction .number)
        else if P.representable n then .ok (.int n)
        else .error (.restriction .range)
      | none =>
        if body.all (isNumeralByte r) then .error (.restriction .number)
        else .error (.error .badToken p)

/-- The datum of a token that begins at offset `p` with neither a parenthesis, a quote, a double
quote, nor `#`: a numeral, a peculiar identifier, an identifier, or a dot, which this function
rejects. -/
def readAtom (P : Profile) (p : Nat) (t : List UInt8) : Except ReadFault Datum :=
  match firstBad t with
  | some i => .error (.error .badByte (p + i))
  | none =>
    if t == [46] then .error (.error .badDot p)
    else if t == [43] || t == [45] || t == [46, 46, 46] then .ok (.sym t)
    else match t with
      | c :: _ =>
        if isDigit c || c == 43 || c == 45 || c == 46 then readNumeral P p t
        else if isInitial c && t.all isSubsequent then .ok (.sym (t.map fold))
        else .error (.error .badToken p)
      | [] => .error (.error .badToken p)

/-- The datum of a token that begins with `#` at offset `p` and continues with neither `(` nor
`\`: a boolean or a prefixed numeral. -/
def readHash (P : Profile) (p : Nat) (t : List UInt8) : Except ReadFault Datum :=
  match firstBad t with
  | some i => .error (.error .badByte (p + i))
  | none =>
    match t.map fold with
    | [35, 116] => .ok (.bool true)
    | [35, 102] => .ok (.bool false)
    | 35 :: k :: _ =>
      if k == 98 || k == 111 || k == 100 || k == 120 || k == 101 || k == 105 then
        readNumeral P p t
      else .error (.error .badHash p)
    | _ => .error (.error .badHash p)

/-- The character after `#\` (§6.6), whose byte is at offset `p`, with the input after it.  `#`
is at offset `p - 2`. -/
def readChar (p : Nat) : List UInt8 → Except ReadFault (Datum × Nat × List UInt8)
  | [] => .error (.error .incomplete p)
  | c :: cs =>
    if c ≥ 128 then .error (.error .badByte p) else
    let (more, rest) := takeToken cs
    if more.isEmpty then .ok (.char c, p + 1, rest)
    else match firstBad more with
      | some i => .error (.error .badByte (p + 1 + i))
      | none =>
        let name := (c :: more).map fold
        if name == bytes "space" then .ok (.char 32, p + 1 + more.length, rest)
        else if name == bytes "newline" then .ok (.char 10, p + 1 + more.length, rest)
        else .error (.error .badChar (p - 2))

/-- The characters of a string after its opening double quote at offset `p - 1` (§6.7), with the
input after the closing double quote.  `acc` holds the characters read so far, last first. -/
def readString : Nat → List UInt8 → List UInt8 → Except ReadFault (Datum × Nat × List UInt8)
  | p, [], _ => .error (.error .incomplete p)
  | p, 34 :: cs, acc => .ok (.str acc.reverse, p + 1, cs)
  | p, [92], _ => .error (.error .incomplete (p + 1))
  | p, 92 :: c :: cs, acc =>
    if c == 34 || c == 92 then readString (p + 2) cs (c :: acc)
    else .error (.error .badString p)
  | p, c :: cs, acc =>
    if c ≥ 128 then .error (.error .badByte p) else readString (p + 1) cs (c :: acc)

/-- Whether the input begins with a dot token: `.` followed by a delimiter or the end. -/
def atDot : List UInt8 → Bool
  | 46 :: [] => true
  | 46 :: c :: _ => isDelimiter c
  | _ => false

/-- The list `(s d)` of an abbreviation (§6.3). -/
def abbreviation (s : String) (d : Datum) : Datum := .pair (.sym (bytes s)) (.pair d .nil)

/-- The result of reading the datum after an abbreviation's prefix, as the list `(s datum)`. -/
def abbreviated (s : String) (r : Except ReadFault (Datum × Nat × List UInt8)) :
    Except ReadFault (Datum × Nat × List UInt8) :=
  r.map fun (d, p, rest) => (abbreviation s d, p, rest)

mutual

/-- One datum after the atmosphere at offset `p`, with the offset and the input after it. -/
def readDatum : Nat → Profile → Nat → List UInt8 → Except ReadFault (Datum × Nat × List UInt8)
  | 0, _, p, _ => .error (.error .incomplete p)
  | fuel + 1, P, p0, input =>
    let (p, bs) := skipAtmosphere false p0 input
    match bs with
    | [] => .error (.error .incomplete p)
    | 40 :: rest => readList fuel P (p + 1) rest []
    | 41 :: _ => .error (.error .unexpectedClose p)
    | 39 :: rest => abbreviated "quote" (readDatum fuel P (p + 1) rest)
    | 96 :: rest => abbreviated "quasiquote" (readDatum fuel P (p + 1) rest)
    | 44 :: 64 :: rest => abbreviated "unquote-splicing" (readDatum fuel P (p + 2) rest)
    | 44 :: rest => abbreviated "unquote" (readDatum fuel P (p + 1) rest)
    | 34 :: rest => readString (p + 1) rest []
    | 35 :: 40 :: rest => readVector fuel P (p + 2) rest []
    | 35 :: 92 :: rest => readChar (p + 2) rest
    | [35] => .error (.error .incomplete (p + 1))
    | c :: rest =>
      let (t, after) := takeToken (c :: rest)
      let d := if c == 35 then readHash P p t else readAtom P p t
      d.map fun d => (d, p + t.length, after)

/-- The elements of a list after its opening parenthesis, through its closing parenthesis.
`acc` holds the elements read so far, last first. -/
def readList : Nat → Profile → Nat → List UInt8 → List Datum →
    Except ReadFault (Datum × Nat × List UInt8)
  | 0, _, p, _, _ => .error (.error .incomplete p)
  | fuel + 1, P, p0, input, acc =>
    let (p, bs) := skipAtmosphere false p0 input
    match bs with
    | [] => .error (.error .incomplete p)
    | 41 :: rest => .ok (Datum.list acc.reverse, p + 1, rest)
    | _ =>
      if atDot bs then
        if acc.isEmpty then .error (.error .badDot p)
        else match readDatum fuel P (p + 1) bs.tail with
          | .error f => .error f
          | .ok (tail, p', rest) =>
            let (q, cs) := skipAtmosphere false p' rest
            match cs with
            | [] => .error (.error .incomplete q)
            | 41 :: after => .ok (Datum.ofList acc.reverse tail, q + 1, after)
            | _ => .error (.error .badDot q)
      else match readDatum fuel P p bs with
        | .error f => .error f
        | .ok (d, p', rest) => readList fuel P p' rest (d :: acc)

/-- The elements of a vector after `#(`, through its closing parenthesis. -/
def readVector : Nat → Profile → Nat → List UInt8 → List Datum →
    Except ReadFault (Datum × Nat × List UInt8)
  | 0, _, p, _, _ => .error (.error .incomplete p)
  | fuel + 1, P, p0, input, acc =>
    let (p, bs) := skipAtmosphere false p0 input
    match bs with
    | [] => .error (.error .incomplete p)
    | 41 :: rest => .ok (.vec (Datum.list acc.reverse), p + 1, rest)
    | _ =>
      if atDot bs then .error (.error .badDot p)
      else match readDatum fuel P p bs with
        | .error f => .error f
        | .ok (d, p', rest) => readVector fuel P p' rest (d :: acc)

end

/-- The data of a program from offset `p`, after those in `acc`, last first. -/
def readAll : Nat → Profile → Nat → List UInt8 → List Datum → Except ReadFault (List Datum)
  | 0, _, p, _, _ => .error (.error .incomplete p)
  | fuel + 1, P, p0, input, acc =>
    let (p, bs) := skipAtmosphere false p0 input
    match bs with
    | [] => .ok acc.reverse
    | 41 :: _ => .error (.error .unexpectedClose p)
    | _ => match readDatum fuel P p bs with
      | .error f => .error f
      | .ok (d, p', rest) => readAll fuel P p' rest (d :: acc)

/-- The data of the program whose bytes are `src` (§5.1, §7.1.2). -/
def readProgram (P : Profile) (src : List UInt8) : Except ReadFault (List Datum) :=
  readAll (src.length + 1) P 0 src []

end Demos.Scheme.Semantics
