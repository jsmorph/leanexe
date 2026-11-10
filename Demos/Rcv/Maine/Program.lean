import Demos.Rcv.Program

/-!
The count of the Maine module over words, in the verified compiler's dialect.  `count` takes a
contest array in the word form of [the requirements](requirements.md), section "Word forms of the
count", and returns the count's result words, or `[0]` for an array that is not a valid contest.
`Demos/Rcv/Maine/Refinement.lean` proves that it equals `Demos.Rcv.Maine.countArray`.

The program shares the functions of the Oakland program of `Demos/Rcv/Program.lean` that the two
counts share: the masks of candidate sets, `classify` of a position word, the 68 counters of a
round, the loops over the candidates `continuingOf`, `majorityOf`, `fewestOf`, `tiedOf`, and
`latestOf`, the round's words of `pushRound`, the counted set of `countedOf` and `countedSize`, and
the test of a valid array `validArray`.  `examineAt` adds rule 1 of the interpretation to the
Oakland examination: it keeps the number of empty positions just passed, up to 2, and a marked
position after two of them ends the examination with `exhausted`.  `tallyRound` examines the first
`m` words of each ballot of `k` words, so that `m = 1` and the continuing set `K` give the first
counts `f(i)` at the votes' counters.  `decideRound` applies the two rules of a round:
`memberCount` gives the number of continuing candidates, `lastPlaceOf` computes rule 2, and two
candidates end the count with the one outside the last place unless they tie, which rule 2 then
decides.  `countValid` appends the first counts to the result words, ends with the winner of the
initial test when `majorityOf` finds a candidate of `K` with `2 f(i) > N`, and otherwise runs the
rounds in a `repeatWhile` as the Oakland program does, with the fuel of `Demos.Rcv.Maine.count`.
-/

namespace Demos.Rcv.Maine.Program

open Demos.Rcv.Program (bitIndex classify continuingOf majorityOf fewestOf tiedOf latestOf
  pushRound countedOf countedSize validArray)

/-- The tally slot of a ballot whose positions from word `p` to word `e - 1` remain to be examined
against the continuing set `cont`, where `seen` is the union of the words of the positions already
passed, `gap` the number of empty positions just before word `p`, counted up to 2, and `counted`
the mask of the counted candidates: 67 at a marked position after two empty ones, rule 1 of the
interpretation, and otherwise the slot of the Oakland program's `examineAt`, `j` when the ballot
counts for candidate `j + 1`, 66 for an overvote, and, when the examination passes the last
position, 64 when every word was 0, 67 when a passed word marks a counted candidate, and 65
otherwise. -/
def examineAt (ws : Array UInt64) (cont counted e p seen gap : UInt64) : UInt64 :=
  if p < e then
    let w := ws[p.toNat]!
    if w == 0 then
      let g : UInt64 := if gap == 0 then 1 else 2
      examineAt ws cont counted e (p + 1) seen g
    else if gap == 2 then 67
    else
      let c := classify w cont
      if c == 0 then examineAt ws cont counted e (p + 1) (seen ||| w) 0 else c - 1
  else if seen == 0 then 64
  else if seen &&& counted != 0 then 67
  else 65
termination_by (e - p).toNat
decreasing_by
  all_goals
    have h : p < e := by assumption
    simp only [UInt64.lt_iff_toNat_lt] at h
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]
    have := UInt64.toNat_lt e
    omega

/-- The 68 counters of a round with the continuing set `cont`: the counter of each of the `N`
ballots' slots, where ballot `b` holds the `k` words from word `base + b k` and the examination
reads its first `m` words. -/
def tallyRound (ws : Array UInt64) (cont counted k m N base : UInt64) : Array UInt64 :=
  LeanExe.loop N (LeanExe.build 68 fun _ => 0) fun b t =>
    let p := base + b * k
    let s := examineAt ws cont counted (p + m) p 0 0
    t.set! s.toNat (t[s.toNat]! + 1)

/-- The number of members of the mask `cont` among the first `n` candidates. -/
def memberCount (cont n : UInt64) : UInt64 :=
  LeanExe.loop n 0 fun c s => if (cont >>> c) &&& 1 != 0 then s + 1 else s

/-- Rule 2 of the rounds, last place, as the code of the elimination, the mask of the eliminated
candidate, the mask of the tied set, and 0: the lowest elimination, code 1, of the continuing
candidate with the fewest votes when it alone has them, and otherwise the elimination by order,
code 2, of the member of the tied set latest in the order, whose `n` indices are the words from
word `3 + n`. -/
def lastPlaceOf (ws t : Array UInt64) (cont n : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
  let f := fewestOf t cont n
  let z := tiedOf t cont n f
  if z.2 == 1 then (1, z.1, 0, 0)
  else
    let l := latestOf ws (3 + n) n z.1
    (2, (1 : UInt64) <<< (l - 1), z.1, 0)

/-- How a round with the counters `t` and the continuing set `cont` ends: the code of the
elimination, 0 when the count ends, 1 lowest, or 2 order, the mask of the eliminated candidate, the
mask of the tied set, and the winner, or 0.  Rule 1, two or fewer: no winner without a continuing
candidate, the candidate alone, and of two candidates the one outside the mask of rule 2's lowest
elimination, or, when they tie, rule 2's elimination by order.  Otherwise rule 2. -/
def decideRound (ws t : Array UInt64) (cont n : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
  let s := memberCount cont n
  if s == 0 then (0, 0, 0, 0)
  else if s == 1 then (0, 0, 0, bitIndex cont + 1)
  else
    let e := lastPlaceOf ws t cont n
    if s == 2 && e.1 == 1 then (0, 0, 0, bitIndex (cont ^^^ e.2.1) + 1) else e

/-- One round from the state `(cont, done, winner, rounds, out)` of a count that has not ended: the
counters of the round, its `Tᵣ`, its end, and its words appended to `out`.  A round that ends the
count records the winner, and any other removes the eliminated candidate from `cont`. -/
@[inline] def roundStep (ws : Array UInt64) (n k N counted : UInt64)
    (s : UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64 :=
  match s with
  | (cont, _, _, r, out) =>
    let t := tallyRound ws cont counted k k N (3 + 2 * n)
    let T := continuingOf t cont n
    let e := decideRound ws t cont n
    let out := pushRound out t cont T n e.1 e.2.1 e.2.2.1
    if e.1 == 0 then (cont, 1, e.2.2.2, r + 1, out)
    else (cont &&& (e.2.1 ^^^ 0xFFFFFFFFFFFFFFFF), 0, 0, r + 1, out)

/-- The result words of a valid contest array: 1, the number of rounds, the first counts `f(1)` to
`f(n)`, the words of each round, and the winner, or 0. -/
def countValid (ws : Array UInt64) : Array UInt64 :=
  let n := ws[(0 : UInt64).toNat]!
  let k := ws[(1 : UInt64).toNat]!
  let N := ws[(2 : UInt64).toNat]!
  let counted := countedOf ws n
  let first := tallyRound ws counted counted k 1 N (3 + 2 * n)
  let out := LeanExe.loop n #[(1 : UInt64), 0] fun c o => o.push first[c.toNat]!
  let w := majorityOf first counted N n
  if w != 0 then out.push w
  else
    let fuel := countedSize ws n + 1
    let s := LeanExe.repeatWhile fuel (counted, (0 : UInt64), (0 : UInt64), (0 : UInt64), out)
      (fun s => s.2.1 == 0) (fun s => roundStep ws n k N counted s)
    match s with
    | (_, _, v, r, out) => (out.set! (1 : UInt64).toNat r).push v

/-- The export over words: the count's result words for a valid contest array, and `[0]` for every
other array. -/
def count (ws : Array UInt64) : Array UInt64 :=
  if validArray ws then countValid ws else #[0]

end Demos.Rcv.Maine.Program
