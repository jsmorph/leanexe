import Demos.Rcv.Maine.Spec

/-!
Executable cases of the Maine specification.  Each `#guard` evaluates the specification when the
module builds.  The expected values come from [the requirements](requirements.md): the 17-ballot
example's file and report and the five-ballot example of the initial test, copied byte for byte,
and small cases of the rules derived by hand.  The House District 58 report needs the corpus, and
`rcv-maine` of `Demos/Rcv/Maine/Native.lean` checks it natively.
-/

namespace Demos.Rcv.Maine.Cases

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Maine

/-- The word of a position that marks the candidates `is`. -/
def pw (is : List Nat) : UInt64 :=
  (is.foldl (fun (acc : Nat) (i : Nat) => acc + (2 : Nat) ^ (i - 1)) 0).toUInt64

/-- A ballot's position words, each position given by the candidates it marks. -/
def bl (fields : List (List Nat)) : List UInt64 := fields.map pw

/-- Lines of ASCII text, each followed by LF. -/
def lines (ls : List String) : List UInt8 :=
  ascii (String.join (ls.map fun l : String => l ++ "\n"))

/-- The structure of a file that the shared reader accepts. -/
def contestOf (b : List UInt8) : Option Contest :=
  match read b with
  | .ok c => some c
  | .error _ _ => none

/-- The report of a file after its first two lines. -/
def afterRule (b : List UInt8) : List UInt8 :=
  match read b with
  | .ok c => text ((reportLines c).drop 2)
  | .error _ _ => []

/-! ## The 17-ballot example -/

def exampleFile : String :=
  "rcv-ballots 1
contest example-maine
positions 4
candidates 5
candidate 1 listed A
candidate 2 listed B
candidate 3 listed C
candidate 4 excluded D
candidate 5 aggregate-writein Write-in
order 1 2 3 4 5
ballots 17
id-01,1,2,,
1,1,1,1
,,1,
5,,1,
4,,2,
4,,,2
,3,,
1|2,3,,
*,1,,
5,,,
4,,,
,,,
2,,,
2,1,,
3,1,,
3,,,1
2,3,,
"

def exampleReport : String :=
  "contest example-maine
positions 4
candidates 5
candidate 1 listed A
candidate 2 listed B
candidate 3 listed C
candidate 4 excluded D
candidate 5 aggregate-writein Write-in
order 1 2 3 4 5
ballots 17
first 1 2
first 2 3
first 3 2
round 1
continuing 10
votes 1 3
votes 2 4
votes 3 3
inactive blank 1
inactive uncounted 2
inactive overvote 2
inactive exhausted 2
tie 1 3
eliminate order 3
round 2
continuing 8
votes 1 4
votes 2 4
inactive blank 1
inactive uncounted 2
inactive overvote 2
inactive exhausted 4
tie 1 2
eliminate order 2
round 3
continuing 5
votes 1 5
inactive blank 1
inactive uncounted 2
inactive overvote 2
inactive exhausted 7
winner 1
"

def ruleLine : String :=
  "rule maine-723a revision 1, 21-A M.R.S. sections 1, 371, 374-A, 696, 722-A, 723-A, and 732 \
    as current through 2026-10-01 (section 723-A as amended by PL 2025 c. 363, effective \
    2025-09-24), 29-250 C.M.R. ch. 535 (effective 2018-11-07), texts read 2026-11-10"

#guard reportFile (ascii exampleFile) =
  ascii ("rcv-report 1\n" ++ ruleLine ++ "\n" ++ exampleReport)

def exampleKinds : List Kind := [.listed, .listed, .listed, .excluded, .aggregateWritein]

/-! Ballot 4 counts for `A`: the write-in at its first position leaves one empty position before
`A`.  Ballot 6 is inactive from round 1: positions 2 and 3 are empty and position 4 is marked.
Ballot 16 counts for `C` in round 1 and is exhausted by rule 1 in round 2. -/

#guard interpret exampleKinds [1, 2, 3] (bl [[5], [], [1], []]) = .counts 1
#guard interpret exampleKinds [1, 2, 3] (bl [[4], [], [], [2]]) = .inactive .exhausted
#guard interpret exampleKinds [1, 2, 3] (bl [[3], [], [], [1]]) = .counts 3
#guard interpret exampleKinds [1, 2] (bl [[3], [], [], [1]]) = .inactive .exhausted

/-! ## The five-ballot example of the initial test -/

def initialFile : String :=
  "rcv-ballots 1
contest initial
positions 2
candidates 3
candidate 1 listed A
candidate 2 listed B
candidate 3 listed C
order 1 2 3
ballots 5
1,2
1,
1,3
,1
2,3
"

#guard afterRule (ascii initialFile) =
  lines ["contest initial", "positions 2", "candidates 3", "candidate 1 listed A",
    "candidate 2 listed B", "candidate 3 listed C", "order 1 2 3", "ballots 5", "first 1 3",
    "first 2 1", "first 3 0", "winner 1"]

#guard (contestOf (ascii initialFile)).map (fun c : Contest => countWords (contestWords c)) =
  some [1, 0, 3, 1, 0, 1]

/-! ## Small cases of the rules -/

/-! Rule 1 needs a later marked position: trailing empty positions end nothing. -/
#guard interpret [.listed, .listed] [2] (bl [[1], [], []]) = .inactive .exhausted
#guard interpret [.listed, .listed] [2] (bl [[], [], []]) = .inactive .blank
#guard interpret [.listed, .listed] [1, 2] (bl [[], [2], [], []]) = .counts 2
#guard interpret [.listed, .listed] [1, 2] (bl [[], [], [2]]) = .inactive .exhausted

/-! An uncounted mark ends a run of empty positions, and a single empty position passes. -/
#guard interpret [.listed, .aggregateWritein] [1] (bl [[2], [], [1]]) = .counts 1
#guard interpret [.listed, .aggregateWritein] [1] (bl [[2], [], [], [1]]) = .inactive .exhausted
#guard interpret [.listed, .aggregateWritein] [1] (bl [[2], [], []]) = .inactive .uncounted

/-! An overvote ends the examination whether or not its candidates continue, and two empty
positions before it exhaust the ballot first. -/
#guard interpret [.listed, .listed, .listed] [1] (bl [[2, 3], [1]]) = .inactive .overvote
#guard interpret [.listed, .listed] [1, 2] ([0, 0, unnamedOvervote]) = .inactive .exhausted

/-! Duplicate rankings: `A,A,,,B` with `A` eliminated is exhausted by rule 1. -/
#guard interpret [.listed, .listed] [2] (bl [[1], [1], [], [], [2]]) = .inactive .exhausted
#guard interpret [.listed, .listed] [2] (bl [[1], [1], [], [2]]) = .counts 2

/-! Rule 1 of the rounds: a tied pair eliminates the one later in the order, and otherwise at most
two candidates end the count. -/
#guard decision [2, 1] ⟨[(1, 3), (2, 3)], 0, 0, 0, 0⟩ = .eliminate (.order [1, 2] 1)
#guard decision [1, 2] ⟨[(1, 0), (2, 0)], 0, 0, 0, 0⟩ = .eliminate (.order [1, 2] 2)
#guard decision [1, 2] ⟨[(1, 2), (2, 3)], 0, 0, 0, 0⟩ = .winner (some 2)
#guard decision [1, 2] ⟨[(1, 0)], 0, 0, 0, 0⟩ = .winner (some 1)
#guard decision [1, 2] ⟨[], 0, 0, 0, 0⟩ = .winner none

/-! Rule 2: three candidates at zero votes, the order eliminating one per round. -/
#guard decision [3, 1, 2] ⟨[(1, 0), (2, 0), (3, 0)], 0, 0, 0, 0⟩ =
  .eliminate (.order [1, 2, 3] 2)
#guard decision [1, 2, 3] ⟨[(1, 1), (2, 5), (3, 4)], 0, 0, 0, 0⟩ = .eliminate (.lowest 1)

/-! The initial test at `2 f(i) = N` elects no one, and at `2 f(i) = N + 1` it elects. -/
#guard initialWinner [.listed, .listed] ((bl [[1], [1], [2], []]).map fun p => [p]) = none
#guard initialWinner [.listed, .listed] ((bl [[1], [1], [2]]).map fun p => [p]) = some 1

/-! An excluded candidate first alone on more than half of the ballots elects no one. -/
#guard initialWinner [.listed, .excluded] ((bl [[2], [2], [1]]).map fun p => [p]) = none
#guard (count [.listed, .excluded] [1, 2] ((bl [[2], [2], [1]]).map fun p => [p])).winner =
  some 1

/-! No counted candidate: one round with no continuing ballot and no winner. -/
#guard count [.excluded] [1] [[pw [1]]] =
  ⟨[⟨⟨[], 0, 1, 0, 0⟩, none⟩], none⟩

/-! No ballots: three listed candidates tie at zero in every round. -/
#guard (count [.listed, .listed, .listed] [1, 2, 3] []).rounds.map Round.elimination =
  [some (.order [1, 2, 3] 3), some (.order [1, 2] 2), none]
#guard (count [.listed, .listed, .listed] [1, 2, 3] []).winner = some 1

end Demos.Rcv.Maine.Cases
