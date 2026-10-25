import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import LeanExe.Pipeline.Implements

/-! A matcher for the regular expressions of `Library.Regex.Spec`, by the position automaton of
McNaughton and Yamada and of Glushkov.  Each set of bytes in a pattern is a position, numbered
from 1 in the order of the pattern, and a state of the automaton is a set of positions held in
one word, bit `p` for position `p` and bit 0 for the start.  `scan` reads the postfix pattern
words once.  It keeps, for each expression on its stack, whether it matches the empty string and
the sets of its first and last positions, and it adds to the follow set of each position the
positions that may come after it.  `matchWith` then builds the positions of each byte and the
unions of follow sets eight bits of a state at a time, and it runs the automaton over the input.
The pattern is the first `pn` words of `pat`, and the input is the first `n` bytes of `msg`,
packed eight to a word as `Library.Bytes` describes. -/

namespace Library.Regex

open LeanExe.Pipeline

/-- The state of the pass over a pattern.  `valid` is false once the pattern fails to decode,
`count` is the number of sets read, `skip` the number of words of the current set still to
read, and `depth` the number of expressions on the stack, which holds three words for each: 1
when it matches the empty string and 0 otherwise, and its first and last positions.  `follow`
holds the follow set of each position and `sets` the four words of each position's set. -/
structure Scan where
  valid : Bool
  count : UInt64
  skip : UInt64
  depth : UInt64
  stack : Array UInt64
  follow : Array UInt64
  sets : Array UInt64
  deriving Inhabited

instance : Flat Scan (Bool × UInt64 × UInt64 × UInt64 × Array UInt64 × Array UInt64 ×
    Array UInt64) :=
  ⟨fun s => (s.valid, s.count, s.skip, s.depth, s.stack, s.follow, s.sets)⟩

/-- `follow` with the positions `next` added to the follow set of each position in `last`. -/
def addFollow (follow : Array UInt64) (last next : UInt64) : Array UInt64 :=
  LeanExe.loop 64 follow fun q f =>
    if (last >>> q) &&& 1 == 1 then f.set! q.toNat (f[q.toNat]! ||| next) else f

/-- The stack with the expression `(empty, first, last)` pushed. -/
def push (s : Scan) (empty first last : UInt64) : Scan :=
  let i := 3 * s.depth
  { s with
    stack := ((s.stack.set! i.toNat empty).set! (i + 1).toNat first).set! (i + 2).toNat last
    depth := s.depth + 1 }

/-- The stack with its top two entries `a` and `b` replaced by the entry `(empty, first, last)`,
and the follow sets of `a`'s last positions extended by `next`. -/
def combine (s : Scan) (empty first last lastA next : UInt64) : Scan :=
  let i := 3 * (s.depth - 2)
  { s with
    stack := ((s.stack.set! i.toNat empty).set! (i + 1).toNat first).set! (i + 2).toNat last
    follow := addFollow s.follow lastA next
    depth := s.depth - 1 }

/-- One word of the pattern. -/
def scanStep (s : Scan) (w : UInt64) : Scan :=
  if !s.valid then s
  else if s.skip != 0 then
    let k := 4 - s.skip
    { s with
      sets := if s.count ≤ 63 then s.sets.set! (4 * s.count + k).toNat w else s.sets
      skip := s.skip - 1 }
  else if w == 0 then push s 0 0 0
  else if w == 1 then push s 1 0 0
  else if w == 2 then
    let count := s.count + 1
    let bit : UInt64 := if count ≤ 63 then (1 : UInt64) <<< count else 0
    push { s with count := count, skip := 4 } 0 bit bit
  else if w == 5 then
    if s.depth == 0 then { s with valid := false }
    else
      let i := 3 * (s.depth - 1)
      let first := s.stack[(i + 1).toNat]!
      let last := s.stack[(i + 2).toNat]!
      { s with
        stack := s.stack.set! i.toNat 1
        follow := addFollow s.follow last first }
  else if w == 3 || w == 4 then
    if s.depth < 2 then { s with valid := false }
    else
      let i := 3 * (s.depth - 2)
      let ea := s.stack[i.toNat]!
      let fa := s.stack[(i + 1).toNat]!
      let la := s.stack[(i + 2).toNat]!
      let eb := s.stack[(i + 3).toNat]!
      let fb := s.stack[(i + 4).toNat]!
      let lb := s.stack[(i + 5).toNat]!
      if w == 3 then
        combine s (ea &&& eb) (fa ||| (if ea == 1 then fb else 0))
          (lb ||| (if eb == 1 then la else 0)) la fb
      else combine s (ea ||| eb) (fa ||| fb) (la ||| lb) 0 0
  else { s with valid := false }

/-- The pass over the first `pn` words of `pat`. -/
def scan (pat : Array UInt64) (pn : UInt64) : Scan :=
  LeanExe.loop pn
    ⟨true, 0, 0, 0, LeanExe.build (3 * pn) (fun _ => 0), LeanExe.build 64 (fun _ => 0),
      LeanExe.build 256 (fun _ => 0)⟩
    fun j s => scanStep s pat[j.toNat]!

/-- For each byte, the positions among the first `count` whose set holds it. -/
def masks (sets : Array UInt64) (count : UInt64) : Array UInt64 :=
  LeanExe.build 256 fun b =>
    LeanExe.loop count 0 fun i acc =>
      let p : UInt64 := i + 1
      let idx : UInt64 := 4 * p + (b >>> (6 : UInt64))
      if (sets[idx.toNat]! >>> (b &&& 63)) &&& 1 == 1 then
        acc ||| ((1 : UInt64) <<< p)
      else acc

/-- The union of the follow sets of the positions in byte `k` of a state, for each byte value
`v`, at index `256 k + v`. -/
def steps (follow : Array UInt64) : Array UInt64 :=
  LeanExe.build 2048 fun idx =>
    let k := idx >>> 8
    let v := idx &&& 255
    LeanExe.loop 8 0 fun j acc =>
      if (v >>> j) &&& 1 == 1 then acc ||| follow[(8 * k + j).toNat]! else acc

/-- The state after the byte `b` from the state `s`. -/
def advance (steps masks : Array UInt64) (s b : UInt64) : UInt64 :=
  let next := LeanExe.loop 8 0 fun k acc =>
    acc ||| steps[(256 * k + ((s >>> (8 * k)) &&& 255)).toNat]!
  next &&& masks[b.toNat]!

/-- The state after the first `n` bytes of `msg`, from the start. -/
def runInput (steps masks : Array UInt64) (msg : Array UInt64) (n : UInt64) : UInt64 :=
  LeanExe.loop n 1 fun i s =>
    advance steps masks s ((msg[(i >>> 3).toNat]! >>> ((i &&& 7) <<< 3)) &&& 255)

/-- The answer of `Library.Regex.Spec.answer` for the first `pn` words of `pat` and the first `n`
bytes of `msg`: 2 when the pattern does not decode, 3 when it has more than 63 sets, and 1 when
the input matches and 0 when it does not. -/
def matchWith (pat : Array UInt64) (pn : UInt64) (msg : Array UInt64) (n : UInt64) : UInt64 :=
  let s := scan pat pn
  if !(s.valid && s.skip == 0 && s.depth == 1) then 2
  else if 63 < s.count then 3
  else
    let follow := s.follow.set! (0 : UInt64).toNat s.stack[(1 : UInt64).toNat]!
    let accept := s.stack[(2 : UInt64).toNat]! |||
      (if s.stack[(0 : UInt64).toNat]! == 1 then 1 else 0)
    if runInput (steps follow) (masks s.sets s.count) msg n &&& accept != 0 then 1 else 0

end Library.Regex
