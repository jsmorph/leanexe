import LeanExe.Dialect.Bytes
import LeanExe.Dialect.Loop

/-!
The reader of the canonical ballot file in the verified compiler's dialect.  `readContest` reads a
buffer of bytes and returns the contest's words of the requirements' section "Word forms of the
count" for a well-formed file, and `#[0, j, code]` for a file whose first faulty line is `j` with
the role of the code `code`: 0 `format`, 1 `contest`, 2 `positions`, 3 `candidates`, 4
`candidate`, 5 `order`, 6 `ballots`, 7 `ballot`, and 8 `end`.  The contest's words start with
`n ≥ 1`, so the first word tells the two results apart.

Each line is the bytes from a position `s` to the position `e` of its LF, which `findByte` finds.
The texts of the format are words of eight bytes, least significant first, that `matchWord`
compares with the buffer.  `readNumber` reads `number = "0" / %x31-39 *DIGIT` and accepts the
values below `2 ^ 64`: before each digit it tests that ten times the value read plus the digit stays
below `2 ^ 64`.  The loops over the numbers of an order line, over the indices of a field, and over
the fields of a ballot line jump from one separator to the next, so they recurse on a count `fuel`,
which is `n` for the first two, since a permutation of 1 to `n` and an increasing list of indices
from 1 to `n` have at most `n` members, and `k` for the third, which the count of commas fixes.  The
loops over the candidate lines and the ballot lines recurse on the number of lines left.  The words
of a well-formed file accumulate in one array: `n`, `k`, and a place for `N`, the kinds, the order,
which fixes `N`'s place by `set!`, and the position words.
-/

namespace Demos.Rcv.ReadProgram

open LeanExe

/-- The first position from `p` below `e` that holds the byte `c`, or `e` when none does. -/
def findByte (b : Bytes) (c p e : UInt64) : UInt64 :=
  if p < e then
    if b.get p == c then p else findByte b c (p + 1) e
  else e
termination_by (e - p).toNat
decreasing_by
  have hlt : p < e := by assumption
  have := UInt64.toNat_lt p
  have := UInt64.toNat_lt e
  simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, UInt64.toNat_add,
    UInt64.reduceToNat] at hlt ⊢
  omega

/-- Byte `i` of `w`, least significant first. -/
def wordByte (w i : UInt64) : UInt64 := (w >>> (8 * i)) &&& 255

/-- Whether the `len` bytes of `b` from `p` are bytes 0 to `len - 1` of `w`. -/
def matchWord (b : Bytes) (p w len : UInt64) : Bool :=
  LeanExe.loop len true fun i ok => ok && b.get (p + i) == wordByte w i

/-- Whether the bytes from `s` to `e` start with bytes 0 to `l1 - 1` of `w1` followed by bytes 0 to
`l2 - 1` of `w2`. -/
def hasPrefix (b : Bytes) (s e w1 l1 w2 l2 : UInt64) : Bool :=
  if l1 + l2 ≤ e - s then matchWord b s w1 l1 && matchWord b (s + l1) w2 l2 else false

/-- The value of the bytes from `s` to `e` with `true` when they are `"0" / %x31-39 *DIGIT` and
the value is below `2 ^ 64`, and `(false, 0)` otherwise.  A value below `2 ^ 64` has at most 20
digits, and ten times `v` plus the digit `d` stays below `2 ^ 64` exactly when `v` is below
1844674407370955161, or equal to it with `d ≤ 5`. -/
def readNumber (b : Bytes) (s e : UInt64) : Bool × UInt64 :=
  if s < e && e - s ≤ 20 && (b.get s != 48 || e - s == 1) then
    let r := LeanExe.loop (e - s) (true, (0 : UInt64)) fun i st =>
      let d := b.get (s + i) - 48
      (st.1 && d < 10 &&
          (st.2 < 1844674407370955161 || (st.2 == 1844674407370955161 && d ≤ 5)),
        10 * st.2 + d)
    if r.1 then r else (false, 0)
  else (false, 0)

/-- Whether the word `x` is a byte of the identifiers' alphabet. -/
def identByteW (x : UInt64) : Bool :=
  (65 ≤ x && x ≤ 90) || (97 ≤ x && x ≤ 122) || (48 ≤ x && x ≤ 57) || x == 45 || x == 95 ||
    x == 46 || x == 58

/-- Whether the bytes from `s` to `e` form an identifier: 1 to 64 bytes of its alphabet. -/
def isIdent (b : Bytes) (s e : UInt64) : Bool :=
  if s < e && e - s ≤ 64 then
    LeanExe.loop (e - s) true fun i ok => ok && identByteW (b.get (s + i))
  else false

/-- Whether the word `x` is a byte of a name: `0x20` to `0x7E`, or `0x80` and above. -/
def nameByteW (x : UInt64) : Bool := (32 ≤ x && x ≤ 126) || 128 ≤ x

/-- Whether the bytes from `s` to `e` form a name: 1 to 255 bytes of its alphabet. -/
def isName (b : Bytes) (s e : UInt64) : Bool :=
  if s < e && e - s ≤ 255 then
    LeanExe.loop (e - s) true fun i ok => ok && nameByteW (b.get (s + i))
  else false

/-- The number after a prefix, `w1` and `w2` of `l1` and `l2` bytes, on the bytes from `s` to `e`,
with `true` when it lies in `[lo, hi]`, and `(false, 0)` otherwise. -/
def readAfter (b : Bytes) (s e w1 l1 w2 l2 lo hi : UInt64) : Bool × UInt64 :=
  if hasPrefix b s e w1 l1 w2 l2 then
    let r := readNumber b (s + l1 + l2) e
    if r.1 && lo ≤ r.2 && r.2 ≤ hi then r else (false, 0)
  else (false, 0)

/-- Line 1: the 13 bytes `rcv-ballots 1`. -/
def isFormat (b : Bytes) (s e : UInt64) : Bool :=
  e - s == 13 && hasPrefix b s e 0x6c6c61622d766372 8 0x312073746f 5

/-- Line 2: `contest ` and an identifier. -/
def isContest (b : Bytes) (s e : UInt64) : Bool :=
  hasPrefix b s e 0x20747365746e6f63 8 0 0 && isIdent b (s + 8) e

/-- The code of the kind word from `s` to `e`: 0 `listed`, 1 `named-writein`, 2
`aggregate-writein`, 3 `excluded`, and 4 for any other bytes. -/
def kindCode (b : Bytes) (s e : UInt64) : UInt64 :=
  if e - s == 6 && matchWord b s 0x64657473696c 6 then 0
  else if e - s == 13 && hasPrefix b s e 0x72772d64656d616e 8 0x6e69657469 5 then 1
  else if e - s == 17 && hasPrefix b s e 0x7461676572676761 8 0x6965746972772d65 8 &&
      matchWord b (s + 16) 0x6e 1 then 2
  else if e - s == 8 && matchWord b s 0x646564756c637865 8 then 3
  else 4

/-- The kind code of the line of candidate `i` from `s` to `e`, or 4 when the line fails its role:
`candidate `, the index, a space, a kind word, a space, and a name. -/
def candidateCode (b : Bytes) (i s e : UInt64) : UInt64 :=
  if hasPrefix b s e 0x74616469646e6163 8 0x2065 2 then
    let q1 := findByte b 32 (s + 10) e
    if q1 < e then
      let q2 := findByte b 32 (q1 + 1) e
      if q2 < e then
        let r := readNumber b (s + 10) q1
        if r.1 && r.2 == i && isName b (q2 + 1) e then kindCode b (q1 + 1) q2 else 4
      else 4
    else 4
  else 4

/-- The indices of an order line from `p` to `e`, each ended by a space or by `e`, pushed onto
`out`.  Each index lies in 1 to `n` and is not in `seen`, the mask of the indices before it, of
which there are `count`, and the flag holds when the last index makes `n` of them.  `fuel` bounds
the indices left, and `n` suffices. -/
def orderFrom (b : Bytes) (n p e seen count fuel : UInt64) (out : Array UInt64) :
    Bool × Array UInt64 :=
  if 0 < fuel then
    let q := findByte b 32 p e
    let r := readNumber b p q
    if r.1 && 1 ≤ r.2 && r.2 ≤ n && (seen >>> (r.2 - 1)) &&& 1 == 0 then
      if q < e then
        orderFrom b n (q + 1) e (seen ||| (1 <<< (r.2 - 1))) (count + 1) (fuel - 1) (out.push r.2)
      else (count + 1 == n, out.push r.2)
    else (false, out)
  else (false, out)
termination_by fuel.toNat
decreasing_by
  have h : 0 < fuel := by assumption
  have h0 := UInt64.lt_iff_toNat_lt.mp h
  simp only [UInt64.reduceToNat] at h0
  simp only [UInt64.toNat_sub, UInt64.reduceToNat]
  have := UInt64.toNat_lt fuel
  omega

/-- The order line from `s` to `e` of a contest with `n` candidates, its indices pushed onto `out`,
with the flag that the line meets its role. -/
def readOrder (b : Bytes) (n s e : UInt64) (out : Array UInt64) : Bool × Array UInt64 :=
  if hasPrefix b s e 0x20726564726f 6 0 0 then orderFrom b n (s + 6) e 0 0 n out
  else (false, out)

/-- The indices of a field from `p` to `e`, each ended by `|` or by `e`, greater than `prev`, the
index before, and at most `n`, with the word `acc` of the indices before them.  `fuel` bounds the
indices left, and `n` suffices. -/
def markFrom (b : Bytes) (n p e prev acc fuel : UInt64) : Bool × UInt64 :=
  if 0 < fuel then
    let q := findByte b 124 p e
    let r := readNumber b p q
    if r.1 && prev < r.2 && r.2 ≤ n then
      if q < e then markFrom b n (q + 1) e r.2 (acc ||| (1 <<< (r.2 - 1))) (fuel - 1)
      else (true, acc ||| (1 <<< (r.2 - 1)))
    else (false, 0)
  else (false, 0)
termination_by fuel.toNat
decreasing_by
  have h : 0 < fuel := by assumption
  have h0 := UInt64.lt_iff_toNat_lt.mp h
  simp only [UInt64.reduceToNat] at h0
  simp only [UInt64.toNat_sub, UInt64.reduceToNat]
  have := UInt64.toNat_lt fuel
  omega

/-- The word of the position field from `s` to `e` of a contest with `n` candidates, with the flag
that the field has the form of a position. -/
def fieldWord (b : Bytes) (n s e : UInt64) : Bool × UInt64 :=
  if s == e then (true, 0)
  else if e - s == 1 && b.get s == 42 then (true, 9223372036854775808)
  else markFrom b n s e 0 0 n

/-- The position fields from `p` to `e`, each ended by a comma or by `e`, their words pushed onto
`out`.  `fuel` bounds the fields left. -/
def fieldsFrom (b : Bytes) (n p e fuel : UInt64) (out : Array UInt64) : Bool × Array UInt64 :=
  if 0 < fuel then
    let q := findByte b 44 p e
    let w := fieldWord b n p q
    if w.1 then
      if q < e then fieldsFrom b n (q + 1) e (fuel - 1) (out.push w.2)
      else (true, out.push w.2)
    else (false, out)
  else (false, out)
termination_by fuel.toNat
decreasing_by
  have h : 0 < fuel := by assumption
  have h0 := UInt64.lt_iff_toNat_lt.mp h
  simp only [UInt64.reduceToNat] at h0
  simp only [UInt64.toNat_sub, UInt64.reduceToNat]
  have := UInt64.toNat_lt fuel
  omega

/-- The number of bytes `c` from `s` to `e`. -/
def countByte (b : Bytes) (c s e : UInt64) : UInt64 :=
  LeanExe.loop (e - s) 0 fun i acc => if b.get (s + i) == c then acc + 1 else acc

/-- The ballot line from `s` to `e` of a contest with `k` positions and `n` candidates, its
position words pushed onto `out`, with the flag that the line meets its role: `k` fields, or an
identifier and `k` fields, by the count of its commas. -/
def ballotWords (b : Bytes) (k n s e : UInt64) (out : Array UInt64) : Bool × Array UInt64 :=
  let commas := countByte b 44 s e
  if commas + 1 == k then fieldsFrom b n s e k out
  else if commas == k then
    let q := findByte b 44 s e
    if isIdent b s q then fieldsFrom b n (q + 1) e k out else (false, out)
  else (false, out)

/-- Lines 1 to 4: 0, `k`, `n`, and the position after line 4, or the number of the first faulty
line and zeros. -/
def readHead (b : Bytes) : UInt64 × UInt64 × UInt64 × UInt64 :=
  let e1 := findByte b 10 0 b.size
  if e1 < b.size && isFormat b 0 e1 then
    let e2 := findByte b 10 (e1 + 1) b.size
    if e2 < b.size && isContest b (e1 + 1) e2 then
      let e3 := findByte b 10 (e2 + 1) b.size
      let k := readAfter b (e2 + 1) e3 0x6e6f697469736f70 8 0x2073 2 1 63
      if e3 < b.size && k.1 then
        let e4 := findByte b 10 (e3 + 1) b.size
        let n := readAfter b (e3 + 1) e4 0x74616469646e6163 8 0x207365 3 1 63
        if e4 < b.size && n.1 then (0, k.2, n.2, e4 + 1) else (4, 0, 0, 0)
      else (3, 0, 0, 0)
    else (2, 0, 0, 0)
  else (1, 0, 0, 0)

/-- The candidate lines from candidate `i` on, `count` of them, from the position `p`, their kind
codes pushed onto `out`: 0, the position after the last of them, and the words, or the number of the
first faulty line. -/
def candidatesFrom (b : Bytes) (p i count : UInt64) (out : Array UInt64) :
    UInt64 × UInt64 × Array UInt64 :=
  if 0 < count then
    let e := findByte b 10 p b.size
    if e < b.size then
      let c := candidateCode b i p e
      if c < 4 then candidatesFrom b (e + 1) (i + 1) (count - 1) (out.push c)
      else (4 + i, 0, out)
    else (4 + i, 0, out)
  else (0, p, out)
termination_by count.toNat
decreasing_by
  have h : 0 < count := by assumption
  have h0 := UInt64.lt_iff_toNat_lt.mp h
  simp only [UInt64.reduceToNat] at h0
  simp only [UInt64.toNat_sub, UInt64.reduceToNat]
  have := UInt64.toNat_lt count
  omega

/-- The ballot lines from line `j` on, `count` of them, from the position `p`, of a contest with `k`
positions and `n` candidates, their position words pushed onto `out`: 0, the position after the last
of them, and the words, or the number of the first faulty line. -/
def ballotsFrom (b : Bytes) (k n p j count : UInt64) (out : Array UInt64) :
    UInt64 × UInt64 × Array UInt64 :=
  if 0 < count then
    let e := findByte b 10 p b.size
    if e < b.size then
      let r := ballotWords b k n p e out
      if r.1 then ballotsFrom b k n (e + 1) (j + 1) (count - 1) r.2
      else (j, 0, r.2)
    else (j, 0, out)
  else (0, p, out)
termination_by count.toNat
decreasing_by
  have h : 0 < count := by assumption
  have h0 := UInt64.lt_iff_toNat_lt.mp h
  simp only [UInt64.reduceToNat] at h0
  simp only [UInt64.toNat_sub, UInt64.reduceToNat]
  have := UInt64.toNat_lt count
  omega

/-- The contest's words of the file `b`, or `#[0, j, code]` for its first faulty line `j` and the
code of its role. -/
def readContest (b : Bytes) : Array UInt64 :=
  let h := readHead b
  if h.1 == 0 then
    let k := h.2.1
    let n := h.2.2.1
    let c := candidatesFrom b h.2.2.2 1 n #[n, k, 0]
    if c.1 == 0 then
      let e := findByte b 10 c.2.1 b.size
      let o := readOrder b n c.2.1 e c.2.2
      if e < b.size && o.1 then
        let e' := findByte b 10 (e + 1) b.size
        let N := readAfter b (e + 1) e' 0x2073746f6c6c6162 8 0 0 0 4294967295
        if e' < b.size && N.1 then
          let r := ballotsFrom b k n (e' + 1) (7 + n) N.2 (o.2.set! (2 : UInt64).toNat N.2)
          if r.1 == 0 then
            if r.2.1 == b.size then r.2.2 else #[0, 7 + n + N.2, 8]
          else #[0, r.1, 7]
        else #[0, 6 + n, 6]
      else #[0, 5 + n, 5]
    else #[0, c.1, 4]
  else #[0, h.1, h.1 - 1]

end Demos.Rcv.ReadProgram
