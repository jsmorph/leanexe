import Demos.Sgp4.Box
import LeanExe.Dialect.Loop

/-!
A reader of two-line element sets.  A line is an array of words that hold one byte each.
`read` checks the layout and the checksum of both lines and returns the fields that the
propagation uses as intervals: each field is a decimal number, read as an integer of its digits
and divided by its power of ten in interval arithmetic.  `TleSound.lean` states the layout and
the values and proves that `read` accepts exactly the lines of that layout and that its intervals
contain the decimal values.

The reader takes the columns of the format: in line 1 the drag term in columns 54 to 61, and in
line 2 the inclination in columns 9 to 16, the right ascension in 18 to 25, the eccentricity in
27 to 33, the argument of perigee in 35 to 42, the mean anomaly in 44 to 51, and the mean motion
in 53 to 63.  It compares the catalog fields of the two lines byte by byte and gives them no
value, so a field in the Alpha-5 form passes.
-/

namespace Demos.Sgp4.Tle

open Library.Numerics.Bounds Library.Numerics.Interval

/-- The byte in column `i`, counted from 0. -/
def byteAt (s : Array UInt64) (i : UInt64) : UInt64 := s[i.toNat]!

def isDigit (c : UInt64) : Bool := decide (48 ≤ c) && decide (c ≤ 57)

/-- The value of a digit, and 0 for any other byte. -/
def digitOf (c : UInt64) : UInt64 := if 48 ≤ c ∧ c ≤ 57 then c - 48 else 0

/-- The number that the `k` bytes from `start` denote, with 0 for a byte that is no digit. -/
def fieldNat (s : Array UInt64) (start k : UInt64) : UInt64 :=
  LeanExe.loop k 0 fun j v => v * 10 + digitOf (byteAt s (start + j))

/-- Whether the `k` bytes from `start` are digits. -/
def allDigits (s : Array UInt64) (start k : UInt64) : Bool :=
  LeanExe.loop k true fun j b => b && isDigit (byteAt s (start + j))

/-- Whether the two bytes from `start` are digits, or a space and a digit. -/
def padded2 (s : Array UInt64) (start : UInt64) : Bool :=
  isDigit (byteAt s (start + 1)) && (isDigit (byteAt s start) || byteAt s start == 32)

/-- Whether the three bytes from `start` are digits after spaces, with a digit last. -/
def padded3 (s : Array UInt64) (start : UInt64) : Bool :=
  isDigit (byteAt s (start + 2)) &&
    ((isDigit (byteAt s (start + 1)) && (isDigit (byteAt s start) || byteAt s start == 32)) ||
      (byteAt s (start + 1) == 32 && byteAt s start == 32))

/-- The checksum of a line: the sum of its digits and of 1 for each minus sign in the first 68
columns, modulo 10. -/
def checksum (s : Array UInt64) : UInt64 :=
  (LeanExe.loop 68 0 fun i acc =>
    let c := byteAt s i
    acc + (if 48 ≤ c ∧ c ≤ 57 then c - 48 else if c == 45 then 1 else 0)) % 10

/-- Whether a line has 69 bytes, begins with the byte `first` and a space, and ends with its
checksum. -/
def framed (s : Array UInt64) (first : UInt64) : Bool :=
  s.size.toUInt64 == 69 && byteAt s 0 == first && byteAt s 1 == 32 &&
    byteAt s 68 == checksum s + 48

/-- Whether line 1 has the layout of the drag term: a space before it, a sign or a space, five
digits, a sign of the exponent, and a digit. -/
def layout1 (s : Array UInt64) : Bool :=
  framed s 49 && byteAt s 52 == 32 &&
    (byteAt s 53 == 32 || byteAt s 53 == 43 || byteAt s 53 == 45) && allDigits s 54 5 &&
    (byteAt s 59 == 43 || byteAt s 59 == 45) && isDigit (byteAt s 60) && byteAt s 61 == 32

/-- Whether line 2 has the layout of its six fields. -/
def layout2 (s : Array UInt64) : Bool :=
  framed s 50 && byteAt s 7 == 32 &&
    padded3 s 8 && byteAt s 11 == 46 && allDigits s 12 4 && byteAt s 16 == 32 &&
    padded3 s 17 && byteAt s 20 == 46 && allDigits s 21 4 && byteAt s 25 == 32 &&
    allDigits s 26 7 && byteAt s 33 == 32 &&
    padded3 s 34 && byteAt s 37 == 46 && allDigits s 38 4 && byteAt s 42 == 32 &&
    padded3 s 43 && byteAt s 46 == 46 && allDigits s 47 4 && byteAt s 51 == 32 &&
    padded2 s 52 && byteAt s 54 == 46 && allDigits s 55 8

/-- Whether the catalog fields of the two lines hold the same bytes. -/
def sameObject (s1 s2 : Array UInt64) : Bool :=
  byteAt s1 2 == byteAt s2 2 && byteAt s1 3 == byteAt s2 3 && byteAt s1 4 == byteAt s2 4 &&
    byteAt s1 5 == byteAt s2 5 && byteAt s1 6 == byteAt s2 6

/-- `10 ^ k` for `k ≤ 19`. -/
def pow10 (k : UInt64) : UInt64 := LeanExe.loop k 1 fun _ p => p * 10

/-- An interval that contains `m / 10 ^ k`. -/
def scaled (m k : UInt64) : Interval := ratio m.toInt64 (pow10 k).toInt64

/-- The drag term: the five digits `m` as `0.m` times ten to the signed exponent. -/
def dragTerm (s : Array UInt64) : Interval :=
  let m := fieldNat s 54 5
  let x := digitOf (byteAt s 60)
  let magnitude :=
    if byteAt s 59 == 45 then scaled m (5 + x)
    else if x ≤ 5 then scaled m (5 - x)
    else ofInt (m * pow10 (x - 5)).toInt64
  if byteAt s 53 == 45 then neg magnitude else magnitude

/-- The fields of an element set: a status, 0 for lines of the layout and 9 otherwise, and the
intervals of the mean motion in revolutions per day, the eccentricity, the inclination, the right
ascension of the node, the argument of perigee, and the mean anomaly in degrees, and the drag
term. -/
structure Fields where
  status : UInt64
  n : Interval
  e : Interval
  incl : Interval
  node : Interval
  argp : Interval
  m : Interval
  bstar : Interval
  deriving Inhabited

/-- The angle in the eight columns from `start`: three columns, a point, and four digits. -/
def angle (s : Array UInt64) (start : UInt64) : Interval :=
  scaled (fieldNat s start 3 * 10000 + fieldNat s (start + 4) 4) 4

def read (s1 s2 : Array UInt64) : Fields :=
  if layout1 s1 && layout2 s2 && sameObject s1 s2 then
    { status := 0
      n := scaled (fieldNat s2 52 2 * 100000000 + fieldNat s2 55 8) 8
      e := scaled (fieldNat s2 26 7) 7
      incl := angle s2 8
      node := angle s2 17
      argp := angle s2 34
      m := angle s2 43
      bstar := dragTerm s1 }
  else ⟨9, rejected, rejected, rejected, rejected, rejected, rejected, rejected⟩

/-- The status and the intervals of the position and the velocity of the element set of two
lines at a time `t` in minutes from its epoch. -/
def propagateWith (inv half logTab expTab : Array UInt64) (s1 s2 : Array UInt64) (t : Interval) :
    Box :=
  let f := read s1 s2
  if f.status == 0 then
    sgp4BoxWith inv half logTab expTab f.n f.e f.incl f.node f.argp f.m f.bstar t
  else noBox f.status

def propagate (s1 s2 : Array UInt64) (t : Interval) : Box :=
  propagateWith Library.Numerics.Float64.Trig.invPi Library.Numerics.Float64.Trig.halfPi
    Library.Numerics.Float64.Pow.powLogTable Library.Numerics.Float64.Exp.expTable s1 s2 t

end Demos.Sgp4.Tle
