module

public import Demos.Scheme.Machine.State
public import Demos.Scheme.Machine.Codes
public import LeanExe.Dialect.Loop

@[expose] public section

/-! Bytes, strings, symbols, and vectors of the executable interpreter: the classes of source
bytes, strings as chunks of packed bytes, the interning of symbols by spelling, and vectors as
chunks of values.  A string's chunk holds 24 bytes in its last three words, eight to a word with
the lowest byte first, and a vector's chunk holds three values. -/

namespace Demos.Scheme.Machine

/-! ## Classes of bytes (§2.2, §7.1.1) -/

@[inline] def isWhite (c : UInt64) : Bool := c == 32 || c == 10 || c == 9 || c == 13 || c == 12

@[inline] def isDelimiter (c : UInt64) : Bool :=
  isWhite c || c == 40 || c == 41 || c == 34 || c == 59

@[inline] def isBadByte (c : UInt64) : Bool := (c < 32 && !isWhite c) || c ≥ 127

@[inline] def foldByte (c : UInt64) : UInt64 := if 65 ≤ c && c ≤ 90 then c + 32 else c

@[inline] def isDigitB (c : UInt64) : Bool := 48 ≤ c && c ≤ 57

@[inline] def isLetterB (c : UInt64) : Bool := 97 ≤ foldByte c && foldByte c ≤ 122

@[inline] def isSpecialInitialB (c : UInt64) : Bool :=
  c == 33 || c == 36 || c == 37 || c == 38 || c == 42 || c == 47 || c == 58 || c == 60 ||
    c == 61 || c == 62 || c == 63 || c == 126 || c == 95 || c == 94

@[inline] def isInitialB (c : UInt64) : Bool := isLetterB c || isSpecialInitialB c

@[inline] def isSubsequentB (c : UInt64) : Bool :=
  isInitialB c || isDigitB c || c == 46 || c == 43 || c == 45

/-- The value of a digit in radix 16, or 16 for another byte. -/
@[inline] def digitValueB (c : UInt64) : UInt64 :=
  if isDigitB c then c - 48
  else if 97 ≤ foldByte c && foldByte c ≤ 102 then foldByte c - 87
  else 16

@[inline] def isNumeralByteB (r c : UInt64) : Bool :=
  digitValueB c < r || c == 35 || c == 46 || c == 47 || c == 43 || c == 45 || c == 64 ||
    foldByte c == 101 || foldByte c == 115 || foldByte c == 102 || foldByte c == 100 ||
    foldByte c == 108 || foldByte c == 105

/-- The offset of the first delimiter at or after `p`, or the end. -/
def tokenEnd (src : LeanExe.Bytes) (p : UInt64) : UInt64 :=
  LeanExe.repeatWhile src.size p (fun q => q < src.size && !isDelimiter (src.get q)) fun q => q + 1

/-- The offset of the first excluded byte from `p` before `e`, or `e`. -/
def firstBadByte (src : LeanExe.Bytes) (p e : UInt64) : UInt64 :=
  LeanExe.repeatWhile src.size p (fun q => q < e && !isBadByte (src.get q)) fun q => q + 1

/-- The offset after whitespace and comments from `p`. -/
def skipAtmosphere (src : LeanExe.Bytes) (p : UInt64) : UInt64 :=
  (LeanExe.repeatWhile src.size (p, false)
    (fun s => s.1 < src.size && (s.2 || isWhite (src.get s.1) || src.get s.1 == 59))
    fun s =>
      let c := src.get s.1
      if s.2 then (s.1 + 1, c != 10) else (s.1 + 1, c == 59)).1

/-- Whether the bytes from `p` to `e` all meet a test: subsequents of an identifier. -/
def allSubsequent (src : LeanExe.Bytes) (p e : UInt64) : Bool :=
  LeanExe.repeatWhile src.size p (fun q => q < e && isSubsequentB (src.get q)) (fun q => q + 1) == e

/-- Whether the bytes from `p` to `e` all are bytes of numerals of radix `r`. -/
def allNumeral (src : LeanExe.Bytes) (r p e : UInt64) : Bool :=
  LeanExe.repeatWhile src.size p (fun q => q < e && isNumeralByteB r (src.get q))
    (fun q => q + 1) == e

/-! ## Strings -/

def CH_VALUES : UInt64 := 1
def CH_BYTES : UInt64 := 2

/-- Byte `i` of a string. -/
def stringByte (heap : Array Slot) (s i : UInt64) : UInt64 :=
  let chunk := LeanExe.repeatWhile (i / 24) (fb heap s) (fun _ => true) fun ch => fa heap ch
  let j := i % 24
  let w := if j < 8 then fb heap chunk else if j < 16 then fc heap chunk else fd heap chunk
  (w >>> (8 * (j % 8))) &&& 255

/-- Word `j` of the packed bytes of a string. -/
def stringWord (heap : Array Slot) (s j : UInt64) : UInt64 :=
  let chunk := LeanExe.repeatWhile (j / 3) (fb heap s) (fun _ => true) fun ch => fa heap ch
  let r := j % 3
  if r == 0 then fb heap chunk else if r == 1 then fc heap chunk else fd heap chunk

/-- The word of the folded source bytes from `p + 8 j` before `e`, the lowest byte first. -/
def sourceWord (src : LeanExe.Bytes) (p e j : UInt64) : UInt64 :=
  (LeanExe.loop 8 (0 : UInt64) fun i w =>
    let q := p + 8 * j + i
    if q < e then w ||| (foldByte (src.get q) <<< (8 * i)) else w)

/-- Word `j` of a candidate spelling: the folded source bytes from `p` to `e` when `entry` is 0,
and otherwise word `j` of the table's entry `entry - 1`. -/
@[inline] def candidateWord (names : Array UInt64) (src : LeanExe.Bytes) (entry p e j : UInt64) :
    UInt64 :=
  if entry != 0 then names[((entry - 1) * 6 + 2 + j).toNat]! else sourceWord src p e j

/-- A string of `len` bytes whose words are those of a candidate spelling, immutable, as the
spelling of a new symbol.  Its reference becomes `val`. -/
def spellingString (names : Array UInt64) (src : LeanExe.Bytes) (m : Machine)
    (entry p e len : UInt64) : Machine :=
  let words := (len + 7) / 8
  let chunks := (words + 2) / 3
  -- the chunks from the last to the first, each linked to the next
  let st := LeanExe.loop chunks (m, NONE) fun i st =>
    let c := chunks - 1 - i
    let m := alloc st.1 (mkKind K_CHUNK CH_BYTES 0) st.2
      (candidateWord names src entry p e (3 * c))
      (if 3 * c + 1 < words then candidateWord names src entry p e (3 * c + 1) else 0)
      (if 3 * c + 2 < words then candidateWord names src entry p e (3 * c + 2) else 0)
    let v := m.val
    (m, v)
  alloc st.1 (mkKind K_STRING 0 0) len st.2 0 0

/-- Whether the spelling of the string `s` is the candidate of `len` bytes. -/
def spellingMatches (names : Array UInt64) (src : LeanExe.Bytes) (heap : Array Slot)
    (s entry p e len : UInt64) : Bool :=
  fa heap s == len &&
    LeanExe.repeatWhile ((len + 7) / 8) (0 : UInt64)
      (fun j => j < (len + 7) / 8 && stringWord heap s j == candidateWord names src entry p e j)
      (fun j => j + 1) == (len + 7) / 8

/-- The entry of the table whose name is the candidate spelling, among the keywords and the
procedures, or the number of entries when no entry has that name. -/
def tableEntry (names : Array UInt64) (src : LeanExe.Bytes) (entry p e len : UInt64) : UInt64 :=
  let n := names.size.toUInt64 / 6
  if len > 32 then n else
  let i := LeanExe.repeatWhile n (0 : UInt64)
    (fun i => i < n && !(names[(i * 6).toNat]! != 0 && names[(i * 6).toNat]! < 1000 &&
      names[(i * 6 + 1).toNat]! == len &&
      names[(i * 6 + 2).toNat]! == candidateWord names src entry p e 0 &&
      names[(i * 6 + 3).toNat]! == candidateWord names src entry p e 1 &&
      names[(i * 6 + 4).toNat]! == candidateWord names src entry p e 2 &&
      names[(i * 6 + 5).toNat]! == candidateWord names src entry p e 3))
    fun i => i + 1
  if i < n then i else n

/-- The symbol whose spelling is the candidate of `len` bytes, interned: the existing symbol, or a
new one whose keyword code and initial top-level value come from the table.  Its reference becomes
`val`. -/
def intern (names : Array UInt64) (src : LeanExe.Bytes) (m : Machine) (entry p e len : UInt64) :
    Machine :=
  let found := LeanExe.repeatWhile m.cap m.syms
    (fun s => s != NONE && !spellingMatches names src m.heap (fa m.heap s) entry p e len)
    fun s => fc m.heap s
  if found != NONE then { m with val := found } else
  let n := names.size.toUInt64 / 6
  let t := if entry != 0 then entry - 1 else tableEntry names src entry p e len
  let code := if t < n then names[(t * 6).toNat]! else 0
  let kw := if 1 ≤ code && code ≤ 20 then code else 0
  let value := if 64 ≤ code && code < 1000 then mkPrim code else UNBOUND
  let m := spellingString names src m entry p e len
  let m := alloc m (mkKind K_SYMBOL kw 0) m.val value m.syms 0
  { m with syms := m.val }

/-- The symbol of a keyword, interned by its entry, whose index is the keyword's code less 1. -/
@[inline] def internKeyword (names : Array UInt64) (src : LeanExe.Bytes) (m : Machine)
    (code : UInt64) : Machine :=
  intern names src m code 0 0 names[((code - 1) * 6 + 1).toNat]!

/-- The keyword code of a symbol, or 0. -/
@[inline] def keywordOf (heap : Array Slot) (v : UInt64) : UInt64 :=
  if isKind heap v K_SYMBOL then subAt heap v else 0

/-! ## Vectors -/

/-- A vector of the elements of the proper list `lst`, with the mutability flag `flag`.  Its
reference becomes `val`. -/
def listToVector (m : Machine) (lst flag : UInt64) : Machine :=
  let n := LeanExe.repeatWhile m.cap (lst, (0 : UInt64)) (fun s => isPair m.heap s.1)
    (fun s => (fb m.heap s.1, s.2 + 1)) |>.2
  let chunks := (n + 2) / 3
  let st := LeanExe.loop chunks (m, NONE) fun i st =>
    let c := chunks - 1 - i
    let e0 := LeanExe.repeatWhile (3 * c) lst (fun _ => true) fun l => fb st.1.heap l
    let e1 := fb st.1.heap e0
    let e2 := fb st.1.heap e1
    let m := alloc st.1 (mkKind K_CHUNK CH_VALUES 0) st.2 (fa st.1.heap e0)
      (if 3 * c + 1 < n then fa st.1.heap e1 else 0) (if 3 * c + 2 < n then fa st.1.heap e2 else 0)
    let v := m.val
    (m, v)
  alloc st.1 (mkKind K_VECTOR 0 0 ||| flag) n st.2 0 0

/-- Element `i` of a vector. -/
def vectorRef (heap : Array Slot) (v i : UInt64) : UInt64 :=
  let chunk := LeanExe.repeatWhile (i / 3) (fb heap v) (fun _ => true) fun ch => fa heap ch
  let r := i % 3
  if r == 0 then fb heap chunk else if r == 1 then fc heap chunk else fd heap chunk

end Demos.Scheme.Machine
