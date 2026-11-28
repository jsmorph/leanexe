module

public import Demos.Scheme.Machine.Numeric

@[expose] public section

/-! The reader of the executable interpreter: one token at each step of the machine, with the
data under construction in frames of the arena, so no traversal depends on the host's stack.  The
reader builds the program's text as immutable data (§3.5): quotations denote it, and `quote`
allocates nothing.  It detects each error at the offset where the reference reader
(`Demos.Scheme.Semantics.readProgram`) detects it, in the same order of tests.

A list frame holds its first pair, its last pair, and a state: 0 before a dot, 1 after a dot,
and 2 after the datum that follows the dot.  A vector frame holds the list of its elements, and an
abbreviation frame its symbol. -/

namespace Demos.Scheme.Machine

def R_LIST : UInt64 := 1
def R_VEC : UInt64 := 2
def R_ABBREV : UInt64 := 3

/-- The machine with `d` appended to the list of the frame `fr`, or to the program's data when
`fr` is `NONE`.  `forms` holds the program's first pair and `aux` its last. -/
def appendElem (m : Machine) (fr d : UInt64) : Machine :=
  let m := alloc m (mkKind K_PAIR 0 0) d NILV 0 0
  let r := m.val
  if fr == NONE then
    let m := if m.forms == NONE then { m with forms := r } else setB m m.aux r
    { m with aux := r }
  else
    let m := if fb m.heap fr == NONE then setB m fr r else setB m (fc m.heap fr) r
    setC m fr r

/-- The machine after the datum `d` is complete: each abbreviation frame on top becomes the list
of its symbol and the datum, and the result joins the list frame, the vector frame, or the
program's data below them. -/
def deliver (m : Machine) (d : UInt64) : Machine :=
  let st := LeanExe.repeatWhile m.cap (m, d)
    (fun st => st.1.status == 0 && st.1.k != NONE && subAt st.1.heap st.1.k == R_ABBREV)
    fun st =>
      let fr := st.1.k
      let m := alloc st.1 (mkKind K_PAIR 0 0) st.2 NILV 0 0
      let m := alloc m (mkKind K_PAIR 0 0) (fb m.heap fr) m.val 0 0
      let next := fa m.heap fr
      let v := m.val
      ({ m with k := next }, v)
  let m := st.1
  let fr := m.k
  if fr != NONE && subAt m.heap fr == R_LIST && fd m.heap fr == 1 then
    setD (setB m (fc m.heap fr) st.2) fr 2
  else appendElem m fr st.2

/-- The string after the double quote at `p - 1` (§6.7): the offset after its closing quote and
its object, or the read error at the first excluded byte, at a backslash before another byte than
`"` or `\`, or at the end of the input. -/
def readString (src : LeanExe.Bytes) (m : Machine) (p : UInt64) : Machine :=
  -- (offset, count, error status, error offset)
  let scan := LeanExe.repeatWhile src.size (p, (0 : UInt64), (0 : UInt64), (0 : UInt64))
    (fun s => s.2.2.1 == 0 && s.1 < src.size && src.get s.1 != 34)
    fun s =>
      let c := src.get s.1
      if c == 92 then
        if s.1 + 1 ≥ src.size then (s.1, s.2.1, S_READ + M_INCOMPLETE, s.1 + 1)
        else if src.get (s.1 + 1) == 34 || src.get (s.1 + 1) == 92 then
          (s.1 + 2, s.2.1 + 1, 0, 0)
        else (s.1, s.2.1, S_READ + M_STRING, s.1)
      else if c ≥ 128 then (s.1, s.2.1, S_READ + M_BYTE, s.1)
      else (s.1 + 1, s.2.1 + 1, 0, 0)
  if scan.2.2.1 != 0 then fail m scan.2.2.1 scan.2.2.2
  else if scan.1 ≥ src.size then fail m (S_READ + M_INCOMPLETE) src.size
  else
    let n := scan.2.1
    let chunks := (n + 23) / 24
    -- the chunks from the first, each filled with 24 bytes of the string and linked from the
    -- previous one: (machine, source offset, first chunk, last chunk)
    let st := LeanExe.loop chunks (m, p, NONE, NONE) fun c st =>
      let w := LeanExe.loop 3 ((0 : UInt64), (0 : UInt64), (0 : UInt64), st.2.1) fun j acc =>
        let b := LeanExe.loop 8 ((0 : UInt64), acc.2.2.2) fun i bs =>
          if 24 * c + 8 * j + i < n then
            let q := bs.2
            let byte := if src.get q == 92 then src.get (q + 1) else src.get q
            (bs.1 ||| (byte <<< (8 * i)), if src.get q == 92 then q + 2 else q + 1)
          else bs
        if j == 0 then (b.1, acc.2.1, acc.2.2.1, b.2)
        else if j == 1 then (acc.1, b.1, acc.2.2.1, b.2)
        else (acc.1, acc.2.1, b.1, b.2)
      let m := alloc st.1 (mkKind K_CHUNK CH_BYTES 0) NONE w.1 w.2.1 w.2.2.1
      let r := m.val
      let m := if st.2.2.2 == NONE then m else setA m st.2.2.2 r
      (m, w.2.2.2, (if st.2.2.1 == NONE then r else st.2.2.1), r)
    let m := alloc st.1 (mkKind K_STRING 0 0) n st.2.2.1 0 0
    deliver { m with pos := scan.1 + 1 } m.val

/-- The token after `#` at `p`, which neither `(` nor `\` follows: a boolean or a prefixed
numeral. -/
def readHash (src : LeanExe.Bytes) (m : Machine) (p : UInt64) : Machine :=
  let e := tokenEnd src p
  let bad := firstBadByte src p e
  if bad < e then fail m (S_READ + M_BYTE) bad
  else
    let k := foldByte (src.get (p + 1))
    if e == p + 2 && k == 116 then deliver { m with pos := e } TRUE
    else if e == p + 2 && k == 102 then deliver { m with pos := e } FALSE
    else if e ≥ p + 2 && (k == 98 || k == 111 || k == 100 || k == 120 || k == 101 || k == 105)
    then
      let r := Numeric.readNumeral src p e
      if r.1 == 0 then deliver { m with pos := e } r.2 else fail m r.1 r.2
    else fail m (S_READ + M_HASH) p

/-- The character after `#\` at `p - 2` (§6.6): the byte at `p`, or the name `space` or
`newline` that the bytes from `p` spell. -/
def readChar (src : LeanExe.Bytes) (m : Machine) (p : UInt64) : Machine :=
  if p ≥ src.size then fail m (S_READ + M_INCOMPLETE) p
  else
    let c := src.get p
    if c ≥ 128 then fail m (S_READ + M_BYTE) p
    else
      let e := tokenEnd src (p + 1)
      if e == p + 1 then deliver { m with pos := e } (mkChar c)
      else
        let bad := firstBadByte src (p + 1) e
        if bad < e then fail m (S_READ + M_BYTE) bad
        else
          let w := sourceWord src p e 0
          if e == p + 5 && w == 435459027059 then deliver { m with pos := e } (mkChar 32)
          else if e == p + 7 && w == 28550371718161774 then deliver { m with pos := e } (mkChar 10)
          else fail m (S_READ + M_CHARNAME) (p - 2)

/-- An atom from `p` that begins with neither a parenthesis, a quote, a double quote, nor `#`: a
peculiar identifier, a numeral, or an identifier (§7.1.1). -/
def readAtom (names : Array UInt64) (src : LeanExe.Bytes) (m : Machine) (p : UInt64) : Machine :=
  let e := tokenEnd src p
  let bad := firstBadByte src p e
  if bad < e then fail m (S_READ + M_BYTE) bad
  else
    let c := src.get p
    let len := e - p
    let peculiar := (len == 1 && (c == 43 || c == 45)) ||
      (len == 3 && c == 46 && src.get (p + 1) == 46 && src.get (p + 2) == 46)
    if peculiar || (isInitialB c && allSubsequent src p e) then
      let m := intern names src m 0 p e len
      deliver { m with pos := e } m.val
    else if isDigitB c || c == 43 || c == 45 || c == 46 then
      let r := Numeric.readNumeral src p e
      if r.1 == 0 then deliver { m with pos := e } r.2 else fail m r.1 r.2
    else fail m (S_READ + M_TOKEN) p

/-- The `)` at `p`. -/
def readClose (m : Machine) (p : UInt64) : Machine :=
  let fr := m.k
  if fr == NONE then fail m (S_READ + M_CLOSE) p
  else
    let sub := subAt m.heap fr
    if sub == R_LIST then
      if fd m.heap fr == 1 then fail m (S_READ + M_CLOSE) p
      else
        let d := if fb m.heap fr == NONE then NILV else fb m.heap fr
        let next := fa m.heap fr
        deliver { m with k := next, pos := p + 1 } d
    else if sub == R_VEC then
      let lst := if fb m.heap fr == NONE then NILV else fb m.heap fr
      let next := fa m.heap fr
      let m := listToVector { m with k := next, pos := p + 1 } lst 0
      deliver m m.val
    else fail m (S_READ + M_CLOSE) p

/-- One token of the program.  At the end of the input the program's data are complete, or a datum
is incomplete. -/
def readStep (names : Array UInt64) (src : LeanExe.Bytes) (m : Machine) : Machine :=
  let p := skipAtmosphere src m.pos
  let fr := m.k
  let listState := if fr != NONE && subAt m.heap fr == R_LIST then fd m.heap fr else 0
  if p ≥ src.size then
    if fr == NONE then
      { m with mode := TOP, pos := p, forms := if m.forms == NONE then NILV else m.forms }
    else fail m (S_READ + M_INCOMPLETE) p
  else
    let c := src.get p
    if listState == 2 && c != 41 then fail m (S_READ + M_DOT) p
    else if c == 40 then pushFrame { m with pos := p + 1 } R_LIST NONE NONE 0
    else if c == 41 then readClose m p
    else if c == 39 then
      let m := internKeyword names src m KW_QUOTE
      pushFrame { m with pos := p + 1 } R_ABBREV m.val 0 0
    else if c == 96 then
      let m := internKeyword names src m KW_QUASIQUOTE
      pushFrame { m with pos := p + 1 } R_ABBREV m.val 0 0
    else if c == 44 && p + 1 < src.size && src.get (p + 1) == 64 then
      let m := internKeyword names src m KW_UNQUOTE_SPLICING
      pushFrame { m with pos := p + 2 } R_ABBREV m.val 0 0
    else if c == 44 then
      let m := internKeyword names src m KW_UNQUOTE
      pushFrame { m with pos := p + 1 } R_ABBREV m.val 0 0
    else if c == 34 then readString src m (p + 1)
    else if c == 35 then
      if p + 1 ≥ src.size then fail m (S_READ + M_INCOMPLETE) (p + 1)
      else if src.get (p + 1) == 40 then pushFrame { m with pos := p + 2 } R_VEC NONE NONE 0
      else if src.get (p + 1) == 92 then readChar src m (p + 2)
      else readHash src m p
    else if c == 46 && (p + 1 ≥ src.size || isDelimiter (src.get (p + 1))) then
      if listState == 0 && fr != NONE && subAt m.heap fr == R_LIST && fb m.heap fr != NONE then
        setD { m with pos := p + 1 } fr 1
      else fail m (S_READ + M_DOT) p
    else readAtom names src m p

end Demos.Scheme.Machine
