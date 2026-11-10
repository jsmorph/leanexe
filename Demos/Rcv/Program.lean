import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import LeanExe.Dialect.RepeatWhile

/-!
The count of the Oakland ranked-choice tabulator over words, in the verified compiler's dialect.
`count` takes a contest array in the word form of the requirements, section "Word forms of the
count", and returns the count's result words, or `[0]` for an array that is not a valid contest.
`Demos/Rcv/Refinement.lean` proves that it equals `Demos.Rcv.Spec.countArray`.

A set of candidates is a mask with bit `i - 1` for candidate `i`, as in the result words.  The
count reads the ballots from the input array in every round.  `examineAt` interprets one ballot
against the continuing set and returns its tally slot: `i - 1` when the ballot counts for candidate
`i`, and 64, 65, 66, or 67 when it is inactive with the reason `blank`, `uncounted`, `overvote`, or
`exhausted`.  It passes empty positions and single positions for candidates outside the continuing
set, and it keeps the union of their words, from which the reason of a ballot that passes its last
position follows: `blank` when the union is 0, `exhausted` when it holds a counted candidate, and
`uncounted` otherwise.  `tallyRound` adds each ballot's slot to an array of 68 counters, so a round
reads each ballot word at most once.

`decideRound` applies the four rules of a round to the counters in `n` or `n²` steps: `majorityOf`
for rule 1, the test of `Tᵣ` for rule 2, `batchOf`, which computes `L(X)` with `lowerOf` for each
continuing `X`, for rule 3, and `fewestOf`, `tiedOf`, and `latestOf` for rule 4.  `pushRound`
appends the round's `n + 9` result words.  `countValid` runs the rounds in a `repeatWhile` whose
state holds the continuing set, whether the count has ended, the winner, the number of rounds, and
the result words, and whose fuel is one more than the number of counted candidates, the fuel of
`Demos.Rcv.Spec.count`.
-/

namespace Demos.Rcv.Program

/-- The position of the set bit of a word with exactly one bit set, found by testing the six bits
of the position in turn. -/
def bitIndex (w : UInt64) : UInt64 :=
  let a : UInt64 := if w &&& 0xFFFFFFFF00000000 != 0 then 32 else 0
  let b : UInt64 := if w &&& 0xFFFF0000FFFF0000 != 0 then 16 else 0
  let c : UInt64 := if w &&& 0xFF00FF00FF00FF00 != 0 then 8 else 0
  let d : UInt64 := if w &&& 0xF0F0F0F0F0F0F0F0 != 0 then 4 else 0
  let e : UInt64 := if w &&& 0xCCCCCCCCCCCCCCCC != 0 then 2 else 0
  let f : UInt64 := if w &&& 0xAAAAAAAAAAAAAAAA != 0 then 1 else 0
  a + b + c + d + e + f

/-- The class of a position word against the continuing set `cont`: 0 when the examination passes
it, that is, when the word is 0 or marks one candidate outside `cont`, `j + 1` when it marks only
the continuing candidate `j + 1`, and 67 when it has bit 63 or two or more bits, an overvote. -/
def classify (w cont : UInt64) : UInt64 :=
  if w == 0 then 0
  else if 0x7FFFFFFFFFFFFFFF < w then 67
  else
    let j := bitIndex w
    if (1 : UInt64) <<< j != w then 67
    else if w &&& cont != 0 then j + 1
    else 0

/-- The tally slot of a ballot whose positions from word `p` to word `e - 1` of `ws` remain to be
examined against the continuing set `cont`, where `seen` is the union of the words of the positions
already passed and `counted` is the mask of the counted candidates: `j` when the ballot counts for
candidate `j + 1`, 66 for an overvote, and, when the examination passes the last position, 64 when
every word was 0, 67 when a passed word marks a counted candidate, and 65 otherwise. -/
def examineAt (ws : Array UInt64) (cont counted e p seen : UInt64) : UInt64 :=
  if p < e then
    let w := ws[p.toNat]!
    let c := classify w cont
    if c == 0 then examineAt ws cont counted e (p + 1) (seen ||| w) else c - 1
  else if seen == 0 then 64
  else if seen &&& counted != 0 then 67
  else 65
termination_by (e - p).toNat
decreasing_by
  have h : p < e := by assumption
  simp only [UInt64.lt_iff_toNat_lt] at h
  simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]
  have := UInt64.toNat_lt e
  omega

/-- The 68 counters of a round with the continuing set `cont`: the counter of each of the `N`
ballots' slots, where ballot `b` holds the `k` words from word `base + b k`. -/
def tallyRound (ws : Array UInt64) (cont counted k N base : UInt64) : Array UInt64 :=
  LeanExe.loop N (LeanExe.build 68 fun _ => 0) fun b t =>
    let p := base + b * k
    let s := examineAt ws cont counted (p + k) p 0
    t.set! s.toNat (t[s.toNat]! + 1)

/-- `Tᵣ`: the sum of the votes of the continuing candidates among the first `n`. -/
def continuingOf (t : Array UInt64) (cont n : UInt64) : UInt64 :=
  LeanExe.loop n 0 fun c acc => if (cont >>> c) &&& 1 != 0 then acc + t[c.toNat]! else acc

/-- Rule 1: the first continuing candidate `i` with `2 vᵣ(i) > Tᵣ`, or 0. -/
def majorityOf (t : Array UInt64) (cont T n : UInt64) : UInt64 :=
  LeanExe.loop n 0 fun c w =>
    if w == 0 && (cont >>> c) &&& 1 != 0 && T < 2 * t[c.toNat]! then c + 1 else w

/-- `L(X)` for a candidate `X` with `v` votes: the mask of the continuing candidates with fewer
votes, the sum of their votes, and their number. -/
def lowerOf (t : Array UInt64) (cont n v : UInt64) : UInt64 × UInt64 × UInt64 :=
  LeanExe.loop n ((0 : UInt64), (0 : UInt64), (0 : UInt64)) fun c s =>
    if (cont >>> c) &&& 1 != 0 && t[c.toNat]! < v then
      (s.1 ||| (1 : UInt64) <<< c, s.2.1 + t[c.toNat]!, s.2.2 + 1)
    else s

/-- Rule 3: the mask and the size of the largest `L(X)` of two or more candidates over the
qualifying `X`, the first of the largest in index order, or `(0, 0)` when there is none. -/
def batchOf (t : Array UInt64) (cont n : UInt64) : UInt64 × UInt64 :=
  LeanExe.loop n ((0 : UInt64), (0 : UInt64)) fun x best =>
    if (cont >>> x) &&& 1 != 0 then
      let v := t[x.toNat]!
      let l := lowerOf t cont n v
      if 2 ≤ l.2.2 && l.2.1 < v && best.2 < l.2.2 then (l.1, l.2.2) else best
    else best

/-- The fewest votes of a continuing candidate, or `2 ^ 64 - 1` when none continues. -/
def fewestOf (t : Array UInt64) (cont n : UInt64) : UInt64 :=
  LeanExe.loop n 0xFFFFFFFFFFFFFFFF fun c m =>
    if (cont >>> c) &&& 1 != 0 && t[c.toNat]! < m then t[c.toNat]! else m

/-- The mask and the number of the continuing candidates with `f` votes. -/
def tiedOf (t : Array UInt64) (cont n f : UInt64) : UInt64 × UInt64 :=
  LeanExe.loop n ((0 : UInt64), (0 : UInt64)) fun c s =>
    if (cont >>> c) &&& 1 != 0 && t[c.toNat]! == f then (s.1 ||| (1 : UInt64) <<< c, s.2 + 1)
    else s

/-- The member of the mask `z` that comes latest in the tie-break order, whose `n` indices are the
words from word `base`, or 0 when the order holds none. -/
def latestOf (ws : Array UInt64) (base n z : UInt64) : UInt64 :=
  LeanExe.loop n 0 fun j l =>
    let o := ws[(base + j).toNat]!
    if (z >>> (o - 1)) &&& 1 != 0 then o else l

/-- How a round with the counters `t`, the continuing set `cont`, and `Tᵣ = T` ends: the code of
the elimination, 0 when the count ends, 1 lowest, 2 order, or 3 batch, the mask of the eliminated
candidates, the mask of the tied set, and the winner, or 0. -/
def decideRound (ws t : Array UInt64) (cont T n : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
  let m := majorityOf t cont T n
  if m != 0 then (0, 0, 0, m)
  else if T == 0 then (0, 0, 0, 0)
  else
    let b := batchOf t cont n
    if b.2 != 0 then (3, b.1, 0, 0)
    else
      let f := fewestOf t cont n
      let z := tiedOf t cont n f
      if z.2 == 1 then (1, z.1, 0, 0)
      else
        let l := latestOf ws (3 + n) n z.1
        (2, (1 : UInt64) <<< (l - 1), z.1, 0)

/-- `out` followed by the `n + 9` words of a round: the continuing set, `Tᵣ`, the votes of the
candidates 1 to `n`, 0 for one outside the continuing set, the four inactive counts, the
elimination's code, the mask of the eliminated candidates, and the mask of the tied set. -/
def pushRound (out t : Array UInt64) (cont T n code elim tie : UInt64) : Array UInt64 :=
  let o := LeanExe.loop n ((out.push cont).push T) fun c o =>
    o.push (if (cont >>> c) &&& 1 != 0 then t[c.toNat]! else 0)
  let o := (o.push t[(64 : UInt64).toNat]!).push t[(65 : UInt64).toNat]!
  let o := (o.push t[(66 : UInt64).toNat]!).push t[(67 : UInt64).toNat]!
  ((o.push code).push elim).push tie

/-- The mask of the counted candidates among the first `n`: those whose kind, from word 3, is 0,
`listed`, or 1, `named-writein`. -/
def countedOf (ws : Array UInt64) (n : UInt64) : UInt64 :=
  LeanExe.loop n 0 fun c m => if ws[(3 + c).toNat]! < 2 then m ||| (1 : UInt64) <<< c else m

/-- The number of counted candidates among the first `n`. -/
def countedSize (ws : Array UInt64) (n : UInt64) : UInt64 :=
  LeanExe.loop n 0 fun c s => if ws[(3 + c).toNat]! < 2 then s + 1 else s

/-- One round from the state `(cont, done, winner, rounds, out)` of a count that has not ended: the
counters of the round, its `Tᵣ`, its end, and its words appended to `out`.  A round that ends the
count records the winner, and any other removes the eliminated candidates from `cont`. -/
@[inline] def roundStep (ws : Array UInt64) (n k N counted : UInt64)
    (s : UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64 :=
  match s with
  | (cont, _, _, r, out) =>
    let t := tallyRound ws cont counted k N (3 + 2 * n)
    let T := continuingOf t cont n
    let e := decideRound ws t cont T n
    let out := pushRound out t cont T n e.1 e.2.1 e.2.2.1
    if e.1 == 0 then (cont, 1, e.2.2.2, r + 1, out)
    else (cont &&& (e.2.1 ^^^ 0xFFFFFFFFFFFFFFFF), 0, 0, r + 1, out)

/-- The result words of a valid contest array: 1, the number of rounds, the words of each round,
and the winner, or 0. -/
def countValid (ws : Array UInt64) : Array UInt64 :=
  let n := ws[(0 : UInt64).toNat]!
  let k := ws[(1 : UInt64).toNat]!
  let N := ws[(2 : UInt64).toNat]!
  let counted := countedOf ws n
  let fuel := countedSize ws n + 1
  let s := LeanExe.repeatWhile fuel
    (counted, (0 : UInt64), (0 : UInt64), (0 : UInt64), #[(1 : UInt64), 0])
    (fun s => s.2.1 == 0) (fun s => roundStep ws n k N counted s)
  match s with
  | (_, _, w, r, out) => (out.set! (1 : UInt64).toNat r).push w

/-- Whether each of the `n` kinds, from word 3, is below 4. -/
def kindsOk (ws : Array UInt64) (n : UInt64) : Bool :=
  LeanExe.loop n true fun c ok => if !ok then false else ws[(3 + c).toNat]! < 4

/-- Whether the `n` words of the tie-break order, from word `3 + n`, are a permutation of 1 to `n`:
each lies in 1 to `n` and none repeats. -/
def orderOk (ws : Array UInt64) (n : UInt64) : Bool :=
  (LeanExe.loop n (true, (0 : UInt64)) fun j s =>
    let o := ws[(3 + n + j).toNat]!
    if s.1 && 1 ≤ o && o ≤ n && (s.2 >>> (o - 1)) &&& 1 == 0 then
      (true, s.2 ||| (1 : UInt64) <<< (o - 1))
    else (false, s.2)).1

/-- Whether each of the `m` position words from word `base` is `2 ^ 63` or below `2 ^ n`. -/
def wordsOk (ws : Array UInt64) (base m n : UInt64) : Bool :=
  LeanExe.loop m true fun p ok =>
    if !ok then false
    else
      let w := ws[(base + p).toNat]!
      w == 0x8000000000000000 || w < (1 : UInt64) <<< n

/-- Whether `ws` is a valid contest array: `n` and `k` from 1 to 63, `N` below `2 ^ 32`,
`3 + 2n + Nk` words, kinds below 4, an order that is a permutation of 1 to `n`, and valid position
words. -/
def validArray (ws : Array UInt64) : Bool :=
  let n := ws[(0 : UInt64).toNat]!
  let k := ws[(1 : UInt64).toNat]!
  let N := ws[(2 : UInt64).toNat]!
  if 1 ≤ n && n ≤ 63 && 1 ≤ k && k ≤ 63 && N ≤ 0xFFFFFFFF &&
      ws.size.toUInt64 == 3 + 2 * n + N * k then
    kindsOk ws n && orderOk ws n && wordsOk ws (3 + 2 * n) (N * k) n
  else false

/-- The export over words: the count's result words for a valid contest array, and `[0]` for every
other array. -/
def count (ws : Array UInt64) : Array UInt64 :=
  if validArray ws then countValid ws else #[0]

end Demos.Rcv.Program
