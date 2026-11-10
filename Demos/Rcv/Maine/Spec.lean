import Demos.Rcv.Read

/-!
The count of the Maine module that [the requirements](requirements.md) state, over shared
definitions: the contest structure and the kinds of `Demos/Rcv/Contest.lean`; the positions, the
counted set, the reasons and `passedReason`, the tally of a round, `latest`, `run`, the lines of the
report, and the word forms of the contest and of a round of `Demos/Rcv/Spec.lean`; and the reader
of `Demos/Rcv/Read.lean`.  `interpret`, the interpretation of a ballot against a continuing set,
adds rule 1, two consecutive empty positions before a marked one, to the examination of the Oakland
module.  `firstCounts` gives `f(i)` of the initial test, `initialWinner` the candidate that the
test elects, and `decision` the two rules that end a round.  `count` ends with the test's winner and
no rounds, or runs `run` with `interpret` and `decision` from `K`.  `reportLines` builds the
report's lines from the shared header, round, and winner lines, with the `first` lines and this
module's rule identifier, `reportFile` gives the report of a file through the shared reader, and
`countWords` is the word form.  Every definition computes, so native Lean runs the specification on
canonical files.

The kinds keep their words, with the meanings of the requirements' table: `named-writein` is a
declared write-in candidate of 21-A M.R.S. §1(11-A) who filed under §722-A and whom the records
name, and `excluded` is an excluded candidate of §723-A(1)(C-1).  The comments of `Kind` give the
Oakland meanings.

The requirements define the count, the file, and the report of a structure that meets
`Contest.WellFormed`, and the result words of a valid array.  The definitions give a value for every
other structure as well, for example for a ballot with a number of positions other than `k`, or
with a position that marks a candidate above `n` alone, which is single and passes.  No requirement
concerns those values, and the theorems that do not assume `Contest.WellFormed` hold for them too.
-/

namespace Demos.Rcv.Maine

open Demos.Rcv Demos.Rcv.Spec

/-! ## Interpretation of a ballot -/

/-- Whether a position is marked: not empty. -/
def marked (w : UInt64) : Bool := position w != .empty

/-- Whether rule 1 applies at an empty position, given the positions after it: the first of them
is empty and some later one is marked. -/
def skipped : List UInt64 → Bool
  | [] => false
  | w :: rest => position w == .empty && rest.any marked

/-- The examination of the positions against the continuing set `C`, from the first position, by
the rules of the interpretation in order: (1) an empty position ends the examination with
`exhausted` when `skipped` holds of the positions after it; (2) any other empty position passes;
(3) a multiple position ends the examination with `overvote`; (4) a single position for a candidate
in `C` ends it with a vote for that candidate; and (5) a single position for any other candidate
passes.  `none` means that the examination passes the last position. -/
def examine (C : List Nat) : List UInt64 → Option Outcome
  | [] => none
  | w :: ws =>
    match position w with
    | .empty => if skipped ws then some (.inactive .exhausted) else examine C ws
    | .multiple => some (.inactive .overvote)
    | .single i => if i ∈ C then some (.counts i) else examine C ws

/-- The interpretation of the ballot with positions `ps` against the continuing set `C`, in a
contest whose candidates have the kinds `kinds`.  A ballot whose examination passes its last
position is inactive with the reason of the Oakland requirements' conditions, `passedReason`. -/
def interpret (kinds : List Kind) (C : List Nat) (ps : List UInt64) : Outcome :=
  (examine C ps).getD (.inactive (passedReason kinds ps))

/-! ## The initial test -/

/-- The first position of a ballot, or empty for a ballot without positions, which no structure
that meets the constraints holds. -/
def firstPosition : List UInt64 → Position
  | [] => .empty
  | w :: _ => position w

/-- `f(i)` for each candidate `i` of `K`, in increasing index: the number of ballots whose first
position is single and marks `i`. -/
def firstCounts (kinds : List Kind) (ballots : List (List UInt64)) : List (Nat × Nat) :=
  let firsts : List Position := ballots.map firstPosition
  (countedSet kinds).map fun i : Nat => (i, firsts.count (.single i))

/-- The candidate that the initial test elects: the candidate `i` of `K` with `2 f(i) > N`, of
which there is at most one, or none. -/
def initialWinner (kinds : List Kind) (ballots : List (List UInt64)) : Option Nat :=
  ((firstCounts kinds ballots).find? fun x : Nat × Nat => ballots.length < 2 * x.2).map
    fun x : Nat × Nat => x.1

/-! ## Rounds -/

/-- Rule 2 of the rounds, last place: the lowest elimination of the candidate with the fewest votes
when it alone has them, and otherwise the elimination by order of the member of the tied set `Z`
latest in the tie-break order `order`, with `Z` marked. -/
def lastPlace (order : List Nat) (votes : List (Nat × Nat)) : Decision :=
  let fewest : Nat := ((votes.map fun x : Nat × Nat => x.2).min?).getD 0
  let Z : List Nat :=
    (votes.filter fun x : Nat × Nat => x.2 = fewest).map fun x : Nat × Nat => x.1
  match Z with
  | [z] => .eliminate (.lowest z)
  | _ => .eliminate (.order Z (latest order Z))

/-- The first of the rules of the rounds that applies to the counts `t` of a round with the
tie-break order `order`.  (1) Two or fewer: two candidates with equal votes are a tied set, and the
one later in the order is eliminated; otherwise at most two candidates end the count, with no winner
when none continues, with the candidate alone, or with the one of more votes.  (2) Last place:
`lastPlace` eliminates one candidate.  A round's votes follow its continuing set, which `run`
filters from `K`, so a tied set lists its members in increasing index, as the report's `tie` line
requires. -/
def decision (order : List Nat) (t : Tally) : Decision :=
  match t.votes with
  | [] => .winner none
  | [x] => .winner (some x.1)
  | [x, y] =>
    if x.2 = y.2 then .eliminate (.order [x.1, y.1] (latest order [x.1, y.1]))
    else if y.2 < x.2 then .winner (some x.1)
    else .winner (some y.1)
  | _ :: _ :: _ :: _ => lastPlace order t.votes

/-- The count of a contest with the kinds `kinds`, the tie-break order `order`, and the ballots'
position words `ballots`.  When the initial test elects `w`, the count has no rounds and names `w`.
Otherwise it runs from round 1 with `C₁ = K`.  Every round that does not end the count eliminates
one member of its continuing set, and a round whose continuing set has at most one member ends
it, so the `K.length + 1` rounds that `run` allows always suffice. -/
def count (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) : Count :=
  match initialWinner kinds ballots with
  | some w => ⟨[], some w⟩
  | none =>
    run (interpret kinds) (decision order) ballots ((countedSet kinds).length + 1)
      (countedSet kinds)

/-- The ballots' position words of a contest structure. -/
def positionsOf (c : Contest) : List (List UInt64) := c.ballots.map fun b : Ballot => b.positions

/-- The count of a contest structure. -/
def countContest (c : Contest) : Count := count (kindsOf c) c.order (positionsOf c)

/-- `f(i)` for each candidate of `K` of a contest structure. -/
def firstContest (c : Contest) : List (Nat × Nat) := firstCounts (kindsOf c) (positionsOf c)

/-! ## The report -/

/-- The rule identifier, printed on the second line of every report of this module. -/
def ruleIdentifier : String :=
  "maine-723a revision 1, 21-A M.R.S. sections 1, 371, 374-A, 696, 722-A, 723-A, and 732 as " ++
    "current through 2026-10-01 (section 723-A as amended by PL 2025 c. 363, effective " ++
    "2025-09-24), 29-250 C.M.R. ch. 535 (effective 2018-11-07), texts read 2026-11-10"

/-- The lines `first i f(i)`, in the order of `first`. -/
def firstLines (first : List (Nat × Nat)) : List (List UInt8) :=
  first.map fun x : Nat × Nat => spaced [ascii "first", decimal x.1, decimal x.2]

/-- The lines of the report of a contest structure: the format line, the rule line, the header
lines of the file, the `first` lines, the lines of each round, and the winner line. -/
def reportLines (c : Contest) : List (List UInt8) :=
  let k : Count := countContest c
  [ascii "rcv-report 1", spaced [ascii "rule", ascii ruleIdentifier]] ++ headerLines c ++
    firstLines (firstContest c) ++
    ((k.rounds.zipIdx 1).flatMap fun p : Round × Nat => roundLines p.2 p.1) ++
    [winnerLine k.winner]

/-- The bytes of the report of a contest structure. -/
def report (c : Contest) : List UInt8 := text (reportLines c)

/-- The error report of a malformed file, whose second line names this module's rule. -/
def errorReport (j : Nat) (r : Role) : List UInt8 :=
  text [ascii "rcv-report 1", spaced [ascii "rule", ascii ruleIdentifier],
    spaced [ascii "error", decimal j, ascii r.word]]

/-- The bytes of the report of the file `b`: the error report when the shared reader rejects `b`,
and the report of the count otherwise. -/
def reportFile (b : List UInt8) : List UInt8 :=
  match read b with
  | .ok c => report c
  | .error j r => errorReport j r

/-! ## Word forms of the count -/

/-- The result words of a count of `n` candidates with the first counts `first`: 1, the number of
rounds, `f(1)` to `f(n)` with 0 for a candidate outside `K`, the words of each round, and the
winner's index or 0. -/
def resultWords (n : Nat) (first : List (Nat × Nat)) (k : Count) : List UInt64 :=
  ([1, k.rounds.length] ++ (List.range' 1 n).map (fun i : Nat => (first.lookup i).getD 0) ++
      k.rounds.flatMap (roundWords n) ++ [k.winner.getD 0]).map Nat.toUInt64

/-- The export over words: the result words of the count for a valid contest array, and `[0]` for
every other array. -/
def countWords (ws : List UInt64) : List UInt64 :=
  let d : Words := readWords ws
  if d.Valid ws.length then
    resultWords d.n (firstCounts (d.kinds.map kindOfCode) d.ballots)
      (count (d.kinds.map kindOfCode) d.order d.ballots)
  else [0]

/-- The export over arrays. -/
def countArray (a : Array UInt64) : Array UInt64 := (countWords a.toList).toArray

end Demos.Rcv.Maine
