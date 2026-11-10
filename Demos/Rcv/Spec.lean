import Demos.Rcv.Contest

/-!
The count of the Oakland ranked-choice tabulator that [the requirements](requirements.md) state,
over lists, natural numbers, and the 64-bit position words, with no reference to a program.
`interpret` is the interpretation of a ballot against a continuing set, `tally` the counts of a
round, `rule` the four rules that end a round, in their order, and `count` the run of rounds to the
winner or to no winner.  `tally` and `run` take the interpretation as an argument, which T10 states
for every interpretation and a module of another statute supplies, and `run` takes the decision of a
round as an argument, which `count` sets to `rule` and the single count of T10 and the county count
of T11 replace.  `write` prints a contest structure as its canonical ballot file, `report`
gives the bytes of the report, whose header lines are the file's, and `countWords` is the word form
of the first increment's export.  Every definition computes, so native Lean runs the specification
on canonical files.

The requirements define the count, the file, and the report of a structure that meets
`Contest.WellFormed`, and the result words of a valid array.  The definitions also give a value for
every other structure, for example a ballot with a number of words other than `k`, a position that
marks a candidate above `n`, or a word with bit 63 and another bit, which `field` prints as `*`, and
no requirement or theorem concerns those values.
-/

namespace Demos.Rcv.Spec

open Demos.Rcv

/-! ## Positions and kinds -/

/-- The candidates that the position word `w` marks: each `i` from 1 to 63 whose bit `i - 1` is
set, in increasing order.  Bit 63, the unnamed overvote, marks no candidate. -/
def marks (w : UInt64) : List Nat :=
  ((List.range 63).filter fun j : Nat => w.toNat.testBit j).map fun j : Nat => j + 1

inductive Position where
  | empty
  | single (i : Nat)
  | multiple
  deriving DecidableEq, Repr

/-- A position is empty when its word is 0, single when it marks exactly one candidate, and
multiple when it marks two or more candidates or holds the unnamed overvote. -/
def position (w : UInt64) : Position :=
  if w.toNat.testBit 63 then .multiple
  else
    match marks w with
    | [] => .empty
    | [i] => .single i
    | _ :: _ :: _ => .multiple

/-- Whether the count counts rankings of a candidate of kind `k`. -/
def countedKind : Kind → Bool
  | .listed => true
  | .namedWritein => true
  | .aggregateWritein => false
  | .excluded => false

/-- `K`, the counted set of a contest whose candidates, in index order, have the kinds `kinds`:
the indices of the candidates of kinds `listed` and `named-writein`, in increasing order. -/
def countedSet (kinds : List Kind) : List Nat :=
  ((List.range' 1 kinds.length).zip kinds).filterMap fun p : Nat × Kind =>
    if countedKind p.2 then some p.1 else none

/-! ## Interpretation of a ballot -/

/-- The reasons for which a ballot is inactive. -/
inductive Reason where
  | blank
  | uncounted
  | overvote
  | exhausted
  deriving DecidableEq, Repr

/-- The interpretation of a ballot: it counts for a candidate, or it is inactive with a reason. -/
inductive Outcome where
  | counts (i : Nat)
  | inactive (r : Reason)
  deriving DecidableEq, Repr

/-- The examination of the positions `ps` against the continuing set `C`, from the first position,
by the rules in order: an empty position passes, a multiple position ends the examination with
`overvote`, a single position for a candidate in `C` ends it with a vote for that candidate, and a
single position for any other candidate passes.  `none` means that the examination passes the last
position. -/
def examine (C : List Nat) : List UInt64 → Option Outcome
  | [] => none
  | w :: ws =>
    match position w with
    | .empty => examine C ws
    | .multiple => some (.inactive .overvote)
    | .single i => if i ∈ C then some (.counts i) else examine C ws

/-- Whether the position word `w` is single and marks a candidate of `K`. -/
def marksCounted (K : List Nat) (w : UInt64) : Bool :=
  match position w with
  | .single i => decide (i ∈ K)
  | _ => false

/-- The reason of a ballot whose examination passes its last position, so that each of its
positions is empty or single: `blank` when every position is empty, `exhausted` when some single
position marks a counted candidate, and otherwise `uncounted`, since then some position is single
and every single position marks an uncounted candidate. -/
def passedReason (kinds : List Kind) (ps : List UInt64) : Reason :=
  if ps.all fun w : UInt64 => position w == .empty then .blank
  else if ps.any (marksCounted (countedSet kinds)) then .exhausted
  else .uncounted

/-- The interpretation of the ballot with positions `ps` against the continuing set `C`, in a
contest whose candidates have the kinds `kinds`. -/
def interpret (kinds : List Kind) (C : List Nat) (ps : List UInt64) : Outcome :=
  (examine C ps).getD (.inactive (passedReason kinds ps))

/-! ## Rounds -/

/-- The counts of a round: each candidate of the continuing set with its votes, in increasing
index, and the inactive ballots by reason. -/
structure Tally where
  votes : List (Nat × Nat)
  blank : Nat
  uncounted : Nat
  overvote : Nat
  exhausted : Nat
  deriving DecidableEq, Repr

/-- `Tᵣ`, the continuing ballots: the sum of the votes. -/
def Tally.continuing (t : Tally) : Nat := (t.votes.map fun x : Nat × Nat => x.2).sum

/-- The counts of a round with the continuing set `C`: every ballot interpreted against `C` by
`interp`, the votes of a candidate the number of ballots that count for it, and each inactive count
the number of ballots inactive with its reason. -/
def tally (interp : List Nat → List UInt64 → Outcome) (C : List Nat) (ballots : List (List UInt64)) :
    Tally :=
  let outcomes : List Outcome := ballots.map (interp C)
  { votes := C.map fun i : Nat => (i, outcomes.count (.counts i))
    blank := outcomes.count (.inactive .blank)
    uncounted := outcomes.count (.inactive .uncounted)
    overvote := outcomes.count (.inactive .overvote)
    exhausted := outcomes.count (.inactive .exhausted) }

/-- The elimination of a round: a batch of rule 3, the single candidate with the fewest votes, or
the member of a tied set latest in the tie-break order. -/
inductive Elimination where
  | batch (members : List Nat)
  | lowest (i : Nat)
  | order (tied : List Nat) (i : Nat)
  deriving DecidableEq, Repr

/-- The candidates that an elimination removes. -/
def Elimination.eliminated : Elimination → List Nat
  | .batch members => members
  | .lowest i => [i]
  | .order _ i => [i]

/-- How a round ends: the count ends with a winner or with none, or the round eliminates. -/
inductive Decision where
  | winner (w : Option Nat)
  | eliminate (e : Elimination)
  deriving DecidableEq, Repr

/-- `L(X)` for a candidate `X` with `v` votes: the continuing candidates with fewer votes, with
their votes. -/
def lower (votes : List (Nat × Nat)) (v : Nat) : List (Nat × Nat) :=
  votes.filter fun y : Nat × Nat => y.2 < v

/-- Whether the candidate `x`, with its votes, qualifies: `L(X)` is not empty and the votes of `X`
exceed the sum of the votes of `L(X)`, the strict test of §1105(f). -/
def qualifies (votes : List (Nat × Nat)) (x : Nat × Nat) : Bool :=
  !(lower votes x.2).isEmpty && ((lower votes x.2).map fun y : Nat × Nat => y.2).sum < x.2

/-- Rule 3: the largest `L(X)` of two or more candidates over the qualifying `X`, in increasing
index, or `none` when no qualifying `X` has two or more candidates in `L(X)`.  The sets `L(X)` are
nested, so the longest is the largest, and the fold keeps the first of the longest. -/
def batch (votes : List (Nat × Nat)) : Option (List Nat) :=
  let sets : List (List Nat) :=
    ((votes.filter (qualifies votes)).map fun x : Nat × Nat =>
        (lower votes x.2).map fun y : Nat × Nat => y.1).filter
      fun s : List Nat => 2 ≤ s.length
  sets.foldl
    (fun (best : Option (List Nat)) (s : List Nat) =>
      match best with
      | some b => if b.length < s.length then some s else some b
      | none => some s)
    none

/-- The member of `Z` that comes latest in the tie-break order `order`: the last element of
`order` that belongs to `Z`.  When `order` is a permutation of 1 to `n` and `Z` is a nonempty set of
candidates, `order` holds every member of `Z`, and the default, the first member of `Z`, is not
used. -/
def latest (order Z : List Nat) : Nat :=
  (order.filter fun i : Nat => decide (i ∈ Z)).getLastD (Z.headD 0)

/-- The first of the rules that applies to the counts `t` of a round with the tie-break order
`order`: (1) a candidate `i` with `2 vᵣ(i) > Tᵣ` wins; (2) with `Tᵣ = 0` the count ends with no
winner; (3) the batch of rule 3; (4) the single candidate with the fewest votes, or, when two or
more have the fewest, the one of them latest in the order, with the tied set marked. -/
def rule (order : List Nat) (t : Tally) : Decision :=
  match t.votes.find? fun x : Nat × Nat => t.continuing < (2 : Nat) * x.2 with
  | some x => .winner (some x.1)
  | none =>
    if t.continuing = 0 then .winner none
    else
      match batch t.votes with
      | some s => .eliminate (.batch s)
      | none =>
        let fewest : Nat := ((t.votes.map fun x : Nat × Nat => x.2).min?).getD 0
        let Z : List Nat :=
          (t.votes.filter fun x : Nat × Nat => x.2 = fewest).map fun x : Nat × Nat => x.1
        match Z with
        | [z] => .eliminate (.lowest z)
        | _ => .eliminate (.order Z (latest order Z))

/-- A round of the count: its counts, and its elimination, which only the last round lacks. -/
structure Round where
  tally : Tally
  elimination : Option Elimination
  deriving DecidableEq, Repr

/-- The rounds of a count, from round 1, and the winner, or none. -/
structure Count where
  rounds : List Round
  winner : Option Nat
  deriving DecidableEq, Repr

/-- The rounds under the interpretation `interp` and the decision `decision`, which ends a round's
count or names its elimination from the round's counts, from the continuing set `C` on, with at
most `fuel` rounds.  The next round's continuing set is `C` minus the eliminated candidates. -/
def run (interp : List Nat → List UInt64 → Outcome) (decision : Tally → Decision)
    (ballots : List (List UInt64)) : Nat → List Nat → Count
  | 0, _ => ⟨[], none⟩
  | fuel + 1, C =>
    let t : Tally := tally interp C ballots
    match decision t with
    | .winner w => ⟨[⟨t, none⟩], w⟩
    | .eliminate e =>
      let rest : Count :=
        run interp decision ballots fuel (C.filter fun i : Nat => decide (i ∉ e.eliminated))
      ⟨⟨t, some e⟩ :: rest.rounds, rest.winner⟩

/-- The count of a contest with the kinds `kinds`, the tie-break order `order`, and the ballots'
position words `ballots`, from round 1 with `C₁ = K`.  A round that does not end the count
eliminates at least one member of its continuing set: a batch has two or more, and a candidate of
rule 4 is a member of the set with the fewest votes, which is not empty since `Tᵣ > 0`.  A round
whose continuing set has one member ends the count by rule 1 or rule 2.  The `K.length + 1` rounds
that `run` allows therefore always suffice, and its case of no round left is never reached. -/
def count (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) : Count :=
  run (interpret kinds) (rule order) ballots ((countedSet kinds).length + 1) (countedSet kinds)

/-- The kinds of a contest's candidates, in index order. -/
def kindsOf (c : Contest) : List Kind := c.candidates.map fun x : Candidate => x.kind

/-- The count of a contest structure, which reads its kinds, its order, and its position words.  It
reads `k` through the ballots, each of which holds `k` position words in a structure that meets the
constraints. -/
def countContest (c : Contest) : Count :=
  count (kindsOf c) c.order (c.ballots.map fun b : Ballot => b.positions)

/-! ## The canonical file and the report -/

/-- The bytes of an ASCII string. -/
def ascii (s : String) : List UInt8 := s.toList.map fun ch : Char => ch.toNat.toUInt8

/-- The decimal form of `n`: `0`, or a nonzero digit followed by digits. -/
def decimal (n : Nat) : List UInt8 := ascii (toString n)

/-- The parts joined by single spaces. -/
def spaced (parts : List (List UInt8)) : List UInt8 := List.intercalate [(0x20 : UInt8)] parts

/-- The lines, each followed by LF. -/
def text (lines : List (List UInt8)) : List UInt8 :=
  lines.flatMap fun line : List UInt8 => line ++ [(0x0A : UInt8)]

def kindWord : Kind → String
  | .listed => "listed"
  | .namedWritein => "named-writein"
  | .aggregateWritein => "aggregate-writein"
  | .excluded => "excluded"

/-- Lines 2 to `6 + n` of the canonical file: the contest, the positions, the number of
candidates, the candidate lines, the order, and the number of ballots. -/
def headerLines (c : Contest) : List (List UInt8) :=
  [spaced [ascii "contest", c.contest], spaced [ascii "positions", decimal c.positions],
      spaced [ascii "candidates", decimal c.candidates.length]] ++
    (c.candidates.zipIdx 1).map (fun p : Candidate × Nat =>
      spaced [ascii "candidate", decimal p.2, ascii (kindWord p.1.kind), p.1.name]) ++
    [spaced (ascii "order" :: c.order.map decimal), spaced [ascii "ballots", decimal c.ballots.length]]

/-- The field of a position word: empty for 0, `*` for the unnamed overvote, and otherwise the
indices that it marks, in increasing order and separated by `|`. -/
def field (w : UInt64) : List UInt8 :=
  if w.toNat.testBit 63 then ascii "*" else List.intercalate (ascii "|") ((marks w).map decimal)

/-- A ballot line: its identifier field when it has one, then its position fields, separated by
commas. -/
def ballotLine (b : Ballot) : List UInt8 :=
  List.intercalate (ascii ",") (b.ident.toList ++ b.positions.map field)

/-- The canonical file of a contest structure. -/
def write (c : Contest) : List UInt8 :=
  text ((ascii "rcv-ballots 1" :: headerLines c) ++ c.ballots.map ballotLine)

/-- The rule identifier, printed on the second line of every report. -/
def ruleIdentifier : String :=
  "oakland-1105 revision 1, Oakland City Charter sections 1103 and 1105 (February 2007), " ++
    "Cal. Elec. Code sections 15341 (updated 1999-01-01) and 15342(d) (updated 2012-01-01), " ++
    "texts read 2026-11-09"

/-- The lines of an elimination, with the candidates of a batch and of a tied set in the order of
the lists, which `rule` gives in increasing index. -/
def eliminationLines : Elimination → List (List UInt8)
  | .batch members => [spaced (ascii "eliminate batch" :: members.map decimal)]
  | .lowest i => [spaced [ascii "eliminate lowest", decimal i]]
  | .order tied i =>
    [spaced (ascii "tie" :: tied.map decimal), spaced [ascii "eliminate order", decimal i]]

/-- The lines of round `r`. -/
def roundLines (r : Nat) (rd : Round) : List (List UInt8) :=
  [spaced [ascii "round", decimal r], spaced [ascii "continuing", decimal rd.tally.continuing]] ++
    rd.tally.votes.map (fun x : Nat × Nat => spaced [ascii "votes", decimal x.1, decimal x.2]) ++
    [spaced [ascii "inactive blank", decimal rd.tally.blank],
      spaced [ascii "inactive uncounted", decimal rd.tally.uncounted],
      spaced [ascii "inactive overvote", decimal rd.tally.overvote],
      spaced [ascii "inactive exhausted", decimal rd.tally.exhausted]] ++
    match rd.elimination with
    | some e => eliminationLines e
    | none => []

def winnerLine : Option Nat → List UInt8
  | some w => spaced [ascii "winner", decimal w]
  | none => ascii "winner none"

/-- The lines of the report of a contest structure. -/
def reportLines (c : Contest) : List (List UInt8) :=
  let k : Count := countContest c
  [ascii "rcv-report 1", spaced [ascii "rule", ascii ruleIdentifier]] ++ headerLines c ++
    ((k.rounds.zipIdx 1).flatMap fun p : Round × Nat => roundLines p.2 p.1) ++ [winnerLine k.winner]

/-- The bytes of the report of a contest structure. -/
def report (c : Contest) : List UInt8 := text (reportLines c)

/-! ## Word forms of the count -/

def kindCode : Kind → Nat
  | .listed => 0
  | .namedWritein => 1
  | .aggregateWritein => 2
  | .excluded => 3

/-- The kind with the code `x`.  A valid contest array has codes below 4. -/
def kindOfCode : Nat → Kind
  | 0 => .listed
  | 1 => .namedWritein
  | 2 => .aggregateWritein
  | _ => .excluded

/-- The contest's words: `n`, `k`, `N`, the kinds, the order, and the position words of each ballot
in turn. -/
def contestWords (c : Contest) : List UInt64 :=
  ([c.candidates.length, c.positions, c.ballots.length] ++
      c.candidates.map (fun x : Candidate => kindCode x.kind) ++ c.order).map Nat.toUInt64 ++
    c.ballots.flatMap fun b : Ballot => b.positions

/-- The parts of a word array at the places of the contest's words: `n`, `k`, and `N` from words
0 to 2, the `n` kinds and the `n` indices of the order after them, and the remaining words.  A
missing header word reads as 0, and the lists of kinds and of the order are shorter than `n` when
the array ends before them. -/
structure Words where
  n : Nat
  k : Nat
  N : Nat
  kinds : List Nat
  order : List Nat
  positions : List UInt64

def readWords (ws : List UInt64) : Words :=
  let n : Nat := (ws.getD 0 0).toNat
  { n
    k := (ws.getD 1 0).toNat
    N := (ws.getD 2 0).toNat
    kinds := ((ws.drop 3).take n).map UInt64.toNat
    order := ((ws.drop (3 + n)).take n).map UInt64.toNat
    positions := ws.drop (3 + 2 * n) }

/-- Whether a word array of `length` words with the parts `d` is a valid contest: `3 + 2n + Nk`
words, `n`, `k`, and `N` in the header's ranges, each kind below 4, the order a permutation of 1 to
`n`, and each position word valid. -/
abbrev Words.Valid (d : Words) (length : Nat) : Prop :=
  1 ≤ d.n ∧ d.n ≤ maxIndex ∧ 1 ≤ d.k ∧ d.k ≤ maxIndex ∧ d.N ≤ maxBallots ∧
  length = 3 + 2 * d.n + d.N * d.k ∧
  (∀ x ∈ d.kinds, x < 4) ∧ d.order.Perm (List.range' 1 d.n) ∧
  ∀ w ∈ d.positions, ValidWord d.n w

/-- `m` consecutive lists of `k` words from the front of `ws`. -/
def chunks (k : Nat) : Nat → List UInt64 → List (List UInt64)
  | 0, _ => []
  | m + 1, ws => ws.take k :: chunks k m (ws.drop k)

/-- The ballots of a valid contest array: `N` lists of `k` position words, in order. -/
def Words.ballots (d : Words) : List (List UInt64) := chunks d.k d.N d.positions

/-- The mask of a set of candidates, with bit `i - 1` for candidate `i`. -/
def mask (s : List Nat) : Nat := (s.map fun i : Nat => (2 : Nat) ^ (i - 1)).sum

/-- The `n + 9` words of a round: the mask of the continuing set, `Tᵣ`, the votes of candidates 1
to `n`, 0 for a candidate outside the continuing set, the four inactive counts, the elimination's
code, the mask of the eliminated candidates, and the mask of the tied set. -/
def roundWords (n : Nat) (rd : Round) : List Nat :=
  [mask (rd.tally.votes.map fun x : Nat × Nat => x.1), rd.tally.continuing] ++
    (List.range' 1 n).map (fun i : Nat => (rd.tally.votes.lookup i).getD 0) ++
    [rd.tally.blank, rd.tally.uncounted, rd.tally.overvote, rd.tally.exhausted] ++
    match rd.elimination with
    | none => [0, 0, 0]
    | some (.lowest i) => [1, mask [i], 0]
    | some (.order tied i) => [2, mask [i], mask tied]
    | some (.batch members) => [3, mask members, 0]

/-- The result words of a count of `n` candidates: 1, the number of rounds, the words of each
round, and the winner's index or 0. -/
def resultWords (n : Nat) (k : Count) : List UInt64 :=
  ([1, k.rounds.length] ++ k.rounds.flatMap (roundWords n) ++ [k.winner.getD 0]).map Nat.toUInt64

/-- The export over words: the result words of the count for a valid contest array, and `[0]` for
every other array. -/
def countWords (ws : List UInt64) : List UInt64 :=
  let d : Words := readWords ws
  if d.Valid ws.length then resultWords d.n (count (d.kinds.map kindOfCode) d.order d.ballots)
  else [0]

/-- The export over arrays. -/
def countArray (a : Array UInt64) : Array UInt64 := (countWords a.toList).toArray

end Demos.Rcv.Spec
